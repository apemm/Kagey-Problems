"""Checks for Section 2 and Appendix A of Paper D (the elephant walk and its crossing).

Model. X_1 is +1 or -1 with probability 1/2. Step t+1 copies a uniformly chosen
earlier step and flips it with probability eps. A_n is the number of +1 steps,
h = n/2, C_n = P(A_n = h) and E_n = P(A_n = n) = (1/2)(1-eps)^(n-1). The
crossing is the eps with C_n = E_n, and x_n = n eps_n.

The numbers that Section 2, Table 1 and Appendix A report are recomputed here. Checks of
numbers from the research notes that the paper no longer prints are kept, labeled
'research notes, not printed'.
Where 2 independent methods were used when the numbers were first found, both are run.

Method A. The minority count M_t (steps that differ from X_1) is a Markov chain
that never decreases. For C_n we keep only the states that can still reach h,
a window of about n/4 states.
Method B. The law of A_t itself with the symmetric start, all states 0..t, no
window and no reduction to M_t.

The Markov walk of Paper A is handled by an exact run-count formula (A) and by
a dynamic program on (A_t, last step) (B).

Run with python -B verify_elephant_crossing.py, or add --full for the second
method at n = 25600 and 51200 and for the slow bridge sums at n = 12800 (research notes).
"""
import argparse
import sys
import time
from fractions import Fraction
from math import comb, exp, lgamma, log, log1p, pi

import mpmath as mp
import numpy as np
from scipy.optimize import brentq
from scipy.special import betaln, gammaln, lambertw, logsumexp

GAMMA = 0.5772156649015329
FAILS = []


def check(label, ok, detail):
    print(('  ok    ' if ok else '  FAIL  ') + label + ': ' + detail, flush=True)
    if not ok:
        FAILS.append(label)


def tol_of(printed):
    """Half a unit in the last printed digit, so a value 'agrees' if it rounds to the print."""
    s = printed.lstrip('+-')
    mant = s.split('e')[0]
    exp10 = int(s.split('e')[1]) if 'e' in s else 0
    dec = len(mant.split('.')[1]) if '.' in mant else 0
    return 0.5 * 10.0 ** (exp10 - dec) * (1 + 1e-9) + 1e-15


def agree(label, printed, values, extra=''):
    """Check that every computed value rounds to the printed paper value."""
    target = float(printed)
    t = tol_of(printed)
    ok = all(abs(v - target) <= t for v in values.values())
    shown = ', '.join(f'{k} {v:.12g}' for k, v in values.items())
    check(label, ok, f'paper {printed}; {shown}{extra}')


# ---------------------------------------------------------------- method A

def center_window(n, eps):
    """C_n = P_+(M_n = h) by the forward window DP on the minority count."""
    h = n // 2
    P = np.zeros(h + 2)
    P[0] = 1.0
    for t in range(1, n):
        lo = max(0, h - (n - t))      # below lo the chain cannot reach h any more
        hi = min(t - 1, h)            # M_t <= t-1, and states above h are useless
        b = np.arange(lo, hi + 1, dtype=float)
        r = eps + (1.0 - 2.0 * eps) * b / t
        seg = P[lo:hi + 1].copy()
        P[lo:hi + 1] = seg * (1.0 - r)
        P[lo + 1:hi + 2] += seg * r
        if lo > 0:
            P[lo - 1] = 0.0
    return P[h]


def center_backward(n, eps):
    """C_n = V_1(0) by the backward value recursion, folded by V_s(b) = V_s(s-b)."""
    h = n // 2
    V = np.zeros(h + 2)
    V[h] = 1.0
    for s in range(n - 1, 0, -1):
        lo, hi = max(0, s - h), s // 2
        b = np.arange(lo, hi + 1)
        r = eps + (1 - 2 * eps) * b / s
        k = b + 1
        kf = np.where(k > (s + 1) // 2, (s + 1) - k, k)
        newV = np.zeros(h + 2)
        newV[lo:hi + 1] = (1 - r) * V[b] + r * V[kf]
        V = newV
    return V[0]


def taylor_window(n, J=3):
    """Taylor coefficients c_0..c_J of C_n in eps, window DP on M_t.
    The up-probability is b/t + eps(1 - 2b/t), so each step is affine in eps."""
    h = n // 2
    C = np.zeros((J + 1, h + 2))
    C[0, 0] = 1.0
    for t in range(1, n):
        lo, hi = max(0, h - (n - t)), min(t - 1, h)
        b = np.arange(lo, hi + 1, dtype=float)
        a0 = b / t
        a1 = 1.0 - 2.0 * b / t
        old = C[:, lo:hi + 1].copy()
        new = np.zeros((J + 1, hi - lo + 2))
        new[:, :-1] += old * (1 - a0)
        new[:, 1:] += old * a0
        new[1:, :-1] -= old[:-1] * a1
        new[1:, 1:] += old[:-1] * a1
        C[:, lo:hi + 2] = new
        if lo > 0:
            C[:, lo - 1] = 0.0
    return C[:, h]


def endpoint(n, eps):
    return 0.5 * exp((n - 1) * log1p(-eps))


# ---------------------------------------------------------------- method B

def law_symmetric(n, eps):
    """Full law of A_n with the symmetric start (index = number of +1 steps)."""
    p = np.array([0.5, 0.5])
    for t in range(1, n):
        f = np.arange(t + 1) / t
        up = f * (1.0 - eps) + (1.0 - f) * eps
        new = np.zeros(t + 2)
        new[:t + 1] = p * (1.0 - up)
        new[1:] += p * up
        p = new
    return p


def taylor_symmetric(n, order=4):
    """Taylor coefficients of P(A_n = h) in eps, on the full symmetric chain A_t."""
    P = np.zeros((order, 2))
    P[0, :] = 0.5
    for t in range(1, n):
        f = np.arange(t + 1) / t
        g = 1.0 - 2.0 * f
        S = np.zeros_like(P)
        S[1:] = P[:-1]
        up = P * f + S * g
        st = P * (1.0 - f) - S * g
        new = np.zeros((order, t + 2))
        new[:, :t + 1] = st
        new[:, 1:] += up
        P = new
    return P[:, n // 2]


# ---------------------------------------------------------------- crossings

def g_root(n):
    """Root of x + log x = 2 log n - log 8, by bisection-type root finding."""
    L = 2 * log(n) - log(8)
    return brentq(lambda x: x + log(x) - L, 1e-9, L + 5, xtol=1e-15)


def g_lambert(n):
    """The same root as W(e^L), since x e^x = e^L."""
    L = 2 * log(n) - log(8)
    return float(lambertw(exp(L)).real)


def x_second(n):
    g = g_root(n)
    return g - (2 * g * log(n) + g * g / 2) / (n * (1 + 1 / g))


def crossing_A(n):
    f = lambda x: log(center_window(n, x / n)) - log(endpoint(n, x / n))
    g = g_root(n)
    return brentq(f, 0.5 * g, g + 0.5, xtol=1e-12)


def crossing_B(n):
    def f(x):
        p = law_symmetric(n, x / n)
        return log(p[n // 2]) - log(p[n])
    g = g_root(n)
    return brentq(f, 0.5 * g, g + 0.5, xtol=1e-12)


def x_refined(n, k2, k3):
    """Refined crossing equation of Remark 2.9 with the next coefficient k3."""
    f = lambda x: (log(4 * x / (n * (n + 2))) + (x / n) * k2 + (x / n) ** 2 * k3
                   - log(0.5) - (n - 1) * log1p(-x / n))
    return brentq(f, 0.3, 5 * log(n), xtol=1e-15)


# ---------------------------------------------------------------- Markov walk (Paper A)

def lbinom(a, b):
    return lgamma(a + 1) - lgamma(b + 1) - lgamma(a - b + 1)


def z_runcount(N):
    """z_N = N(1 - p_N) from 2 sum_k W_k u^k = 1 with u = q/p, where W_k counts the
    words with h pluses, h minuses, first letter + and k switches."""
    h = N // 2
    ks, lw = [], []
    for r in range(1, h + 1):
        ks.append(2 * r - 1)
        lw.append(2 * lbinom(h - 1, r - 1))
        if r >= 2:
            ks.append(2 * r - 2)
            lw.append(lbinom(h - 1, r - 1) + lbinom(h - 1, r - 2))
    ks, lw = np.array(ks, float), np.array(lw)
    lu = brentq(lambda s: log(2.0) + logsumexp(lw + ks * s), -60.0, 5.0, xtol=1e-15)
    u = exp(lu)
    return N * u / (1 + u), 1 / (1 + u)


def markov_center_end(N, p):
    plus = np.zeros(N + 1)
    minus = np.zeros(N + 1)
    plus[1] = 0.5
    minus[0] = 0.5
    q = 1.0 - p
    for t in range(1, N):
        np_ = np.zeros(N + 1)
        nm = np.zeros(N + 1)
        np_[1:t + 2] = plus[0:t + 1] * p + minus[0:t + 1] * q
        nm[0:t + 1] = minus[0:t + 1] * p + plus[0:t + 1] * q
        plus, minus = np_, nm
    tot = plus + minus
    return tot[N // 2], tot[N]


def z_dp(N):
    L = log(N)

    def F(p):
        c, e = markov_center_end(N, p)
        return log(c) - log(e)
    p = brentq(F, 1 - 3 * L / N, 1 - 0.2 * L / N, xtol=1e-16, rtol=1e-15)
    return N * (1 - p), p


# ---------------------------------------------------------------- bounds of Theorem 2.6

def log_pi(n, t):
    """pi_t = t prod_{i<t}(h-i) / prod_{i<=t}(n-i)."""
    h = n // 2
    return log(t) + lgamma(h) - lgamma(h - t + 1) + lgamma(n - t) - lgamma(n)


def upper_A(n, eps):
    """U_n of Proposition A.4(d), the upper bound behind Theorem 2.6(b), with the weights w_t = pi_t/c_1 from lgamma."""
    kap = 2 * eps / (1 - 4 * eps)
    h = n // 2
    ts = np.arange(1, h + 1, dtype=float)
    c1 = 4.0 / (n + 2)
    w = np.exp([log_pi(n, int(t)) for t in ts]) / c1
    Ht = np.cumsum(1.0 / ts)
    G = (ts + 11) * (np.log((ts + 1) ** 2 / (4 * ts)) + 2 / 3) - Ht + 2 / (3 * ts)
    S = np.sum(w * np.exp((ts - 1) * log1p(-eps) + kap * G))
    return eps * c1 * exp(kap * np.sum(1.0 / np.arange(1, n))) * S


def upper_B(n, eps):
    """The same bound, with pi_t = t C(n-t-1, h-1) B(h, h) from betaln."""
    h = n // 2
    t = np.arange(1, h + 1).astype(float)
    lc = gammaln(n - t) - gammaln(h) - gammaln(n - t - h + 1)
    p = np.exp(np.log(t) + lc + betaln(h, h))
    c1 = 4.0 / (n + 2)
    kap = 2 * eps / (1 - 4 * eps)
    Ht = np.cumsum(1.0 / t)
    G = (t + 11) * (np.log((t + 1) ** 2 / (4 * t)) + 2.0 / 3) - Ht + 2.0 / (3 * t)
    Hn1 = float(np.sum(1.0 / np.arange(1, n)))
    return eps * c1 * exp(kap * Hn1) * np.sum(p / c1 * (1 - eps) ** (t - 1) * np.exp(kap * G))


def bridge_A(n, t):
    """Bridge sums A_t and B_t (research notes behind Remark 2.9, not printed), by a forward DP of the bridge from (t+1, 1) to (n, h)."""
    h = n // 2
    P = np.zeros(h + 2)
    P[1] = 1.0
    A = B = 0.0
    for u in range(t + 1, n):
        lo, hi = max(1, u - h), min(h, u - t)
        b = np.arange(lo, hi + 1, dtype=float)
        p = P[lo:hi + 1]
        f = b / u
        pr = (h - b) / (n - u)
        A += np.dot(p, n * (u - 2 * b) ** 2 / (2.0 * (n - u) * b * (u - b)))
        B += np.dot(p, (1 - 2 * f) ** 2 * (pr / f ** 2 + (1 - pr) / (1 - f) ** 2))
        seg = p.copy()
        P[lo:hi + 1] = seg * (1 - pr)
        P[lo + 1:hi + 2] += seg * pr
        P[:lo] = 0.0
    return A, B


def bridge_B(n, t):
    """The same sums, with b_u - 1 hypergeometric (N = n-t-1, K = h-1, u-t-1 draws)."""
    h = n // 2
    N, K = n - t - 1, h - 1
    A = B = 0.0
    lc = lambda a, b: gammaln(a + 1) - gammaln(b + 1) - gammaln(a - b + 1)
    for u in range(t + 1, n):
        m = u - t - 1
        k = np.arange(max(0, m - (N - K)), min(m, K) + 1)
        pk = np.exp(lc(K, k) + lc(N - K, m - k) - lc(N, m))
        b = (k + 1).astype(float)
        f = b / u
        pr = (h - b) / (n - u)
        A += np.dot(pk, n * (u - 2 * b) ** 2 / (2.0 * (n - u) * b * (u - b)))
        B += np.dot(pk, (1 - 2 * f) ** 2 * (pr / f ** 2 + (1 - pr) / (1 - f) ** 2))
    return A, B


def jensen(n, eps, AB):
    """J_n, the bridge lower bound of the research notes (Remark 2.9, not printed), summed over t <= 60."""
    s = 0.0
    for t, (A, B) in AB.items():
        s += exp((t - 1) * log1p(-eps) + log_pi(n, t) + eps * A - eps ** 2 * B)
    return eps * s


# ---------------------------------------------------------------- exact small cases

def center_fraction(n, eps):
    """C_n in exact rationals (fixed-start minority chain, no window)."""
    P = [Fraction(1)] + [Fraction(0)] * n
    for t in range(1, n):
        new = [Fraction(0)] * (n + 1)
        for b in range(t):
            if P[b]:
                r = eps + (1 - 2 * eps) * Fraction(b, t)
                new[b] += P[b] * (1 - r)
                new[b + 1] += P[b] * r
        P = new
    return P[n // 2]


def center_mpmath(n, eps, dps=40):
    """C_n with 40-digit arithmetic on the symmetric chain."""
    mp.mp.dps = dps
    e = mp.mpf(eps)
    p = [mp.mpf(1) / 2, mp.mpf(1) / 2]
    for t in range(1, n):
        new = [mp.mpf(0)] * (t + 2)
        for a in range(t + 1):
            f = mp.mpf(a) / t
            up = f * (1 - e) + (1 - f) * e
            new[a] += p[a] * (1 - up)
            new[a + 1] += p[a] * up
        p = new
    return p[n // 2]


def exact_checks():
    print('\nExactness of the engines (Section 5)', flush=True)
    worst = 0.0
    for n in (10, 30, 60):
        for eps in (Fraction(1, 20), Fraction(3, 100)):
            ex = center_fraction(n, eps)
            worst = max(worst, abs(center_window(n, float(eps)) / float(ex) - 1))
    check('window DP against exact rationals, n = 10, 30, 60', worst < 1e-12,
          f'largest relative difference {worst:.1e}')
    x = 7.6292168962
    cm = center_mpmath(400, x / 400)
    rel = abs(center_window(400, x / 400) / float(cm) - 1)
    check('window DP against 40-digit arithmetic at n = 400', rel < 1e-10, f'relative difference {rel:.1e}')
    for n, x in ((6400, 12.8524830457), (12800, 14.1588452626)):
        cf, cb = center_window(n, x / n), center_backward(n, x / n)
        rel = abs(cf / cb - 1)
        check(f'forward window DP and folded backward DP at n = {n}', rel < 2e-14,
              f'relative difference {rel:.1e} (Section 5 quotes agreement to about 1e-14 at n = 12800)')

    # c_1 = 4/(n+2): exact sum of pi_t, and the exact first Taylor coefficient.
    ok = True
    for n in range(4, 81, 2):
        h = n // 2
        s = Fraction(0)
        for t in range(1, h + 1):
            v = Fraction(t)
            for i in range(1, t):
                v *= Fraction(h - i)
            for i in range(1, t + 1):
                v /= Fraction(n - i)
            s += v
        ok &= (s == Fraction(4, n + 2))
    check('c_1 = sum_t pi_t = 4/(n+2) exactly, every even n <= 80', ok, 'exact rationals')
    worst = 0.0
    for n in (100, 1600, 12800):
        c = taylor_window(n, 1)
        worst = max(worst, abs(c[1] * (n + 2) / 4 - 1))
    c = taylor_symmetric(1600, 2)
    worst = max(worst, abs(c[1] * 1602 / 4 - 1))
    check('c_1 (n+2)/4 = 1 from both Taylor DPs, n = 100, 1600, 12800', worst < 1e-12,
          f'largest deviation {worst:.1e}')

    # Proposition 2.5(c): sum_t w_t t = 3 - 6/(h+2) exactly. The bound sum_t w_t (t+1)^3 <= 124 is research notes, not printed.
    ok = True
    for n in range(4, 201, 2):
        h = n // 2
        wt = [Fraction(t * comb(n - 1 - t, h - 1)) for t in range(1, h + 1)]
        tot = sum(wt)
        ok &= (sum(Fraction(t) * w for t, w in zip(range(1, h + 1), wt)) / tot == 3 - Fraction(6, h + 2))
    check('sum_t w_t t = 3 - 6/(h+2), every even n <= 200 (Proposition 2.5(c))', ok, 'exact rationals')
    big = 0.0
    for n in range(4, 20001, 2):
        h = n // 2
        T = min(h, 200)
        ts = np.arange(1, T + 1, dtype=float)
        lw = np.array([log_pi(n, int(t)) for t in ts]) - log(4 / (n + 2))
        big = max(big, float(np.sum(np.exp(lw) * (ts + 1) ** 3)))
    lim = sum(t * 2.0 ** (-t - 1) * (t + 1) ** 3 for t in range(1, 400))
    check('sum_t w_t (t+1)^3 <= 124 for every even n <= 20000 (research notes, not printed)', big <= 124,
          f'largest value {big:.3f}, limit n -> oo {lim:.3f} (t <= 200 kept; the rest is below 1e-40)')


# ---------------------------------------------------------------- proof constants

def proof_constants():
    print('\nConstants in the proof of Theorem 2.6 (Appendix A, and the explicit constants of the research notes)', flush=True)
    s = sum(t * (t + 11) * log(t + 1) * 2.0 ** (-t / 2) for t in range(1, 400))
    mp.mp.dps = 30
    s2 = float(mp.nsum(lambda t: t * (t + 11) * mp.log(t + 1) * mp.power(2, -t / 2), [1, mp.inf]))
    check('sum_t t(t+11) log(t+1) 2^(-t/2) <= 261.91 (research notes, not printed)', s <= 261.91 and abs(s - s2) < 1e-9,
          f'direct sum {s:.6f}, mpmath nsum {s2:.6f} (notes 261.9013)')
    S3 = float(mp.nsum(lambda t: t ** 2 * mp.log(t + 1) * mp.power(2, -t / 2), [1, mp.inf]))
    S3d = sum(t * t * log(t + 1) * 2.0 ** (-t / 2) for t in range(1, 400))
    agree('sum_t t^2 log(t+1) 2^(-t/2) = 102.59 (proof of Theorem 2.6(b))', '102.59', {'mpmath nsum': S3, 'direct sum': S3d})
    # The rigorous bound in the proof: the first 60 terms, and a geometric tail from the ratio at t >= 60.
    term = lambda t: mp.mpf(t) ** 2 * mp.log(t + 1) * mp.power(2, -mp.mpf(t) / 2)
    ratio = lambda t: (1 + mp.mpf(1) / t) ** 2 * mp.log(t + 2) / mp.log(t + 1) / mp.sqrt(2)
    S60 = mp.fsum(term(t) for t in range(1, 61))
    agree('first 60 terms of sum_t t^2 log(t+1) 2^(-t/2) (proof of Theorem 2.6(b))', '102.5864', {'exact sum, 30 digits': float(S60)})
    rats = [ratio(t) for t in range(1, 2001)]
    check('ratio of consecutive terms decreases in t and is below 3/4 at t = 60 (proof of Theorem 2.6(b))',
          all(a > b for a, b in zip(rats, rats[1:])) and rats[59] < 0.75, f'ratio at t = 60: {float(rats[59]):.4f}')
    check('4 times the term at t = 61 is below 1e-4 (proof of Theorem 2.6(b))', 4 * term(61) < 1e-4,
          f'{float(4 * term(61)):.2e}; so the series is below {float(S60 + 4 * term(61)):.6f} < 102.59')
    check('3 + 50.4 * 102.59 < 5200 (proof of Theorem 2.6(b))', 3 + 50.4 * 102.59 < 5200 and S3 < 102.59,
          f'{3 + 50.4 * 102.59:.2f}')
    Ht, okG = 0.0, True
    for t in range(1, 10 ** 5 + 1):
        Ht += 1.0 / t
        okG &= (2 / 3) * (t + 11) > 1 + log(t) >= Ht - 1e-12
    check('(2/3)(t+11) > 1 + log t >= H_t for 1 <= t <= 1e5 (proof of Theorem 2.6(b))', okG, 'direct')
    v = 2.084 * 1.032 * 261.91
    check('2.084 * 1.032 * 261.91 <= 563.3 (research notes, not printed)', v <= 563.3, f'{v:.3f}')
    kap = 2 / (1 - 4 / 100)
    check('kappa <= 2.084 eps when eps <= 1/100 (research notes, not printed)', kap <= 2.084, f'2/(1-4/100) = {kap:.5f}')
    check('1 + 2/n <= 1.032 for n >= 64 (research notes, not printed)', 1 + 2 / 64 <= 1.032, f'1 + 2/64 = {1 + 2 / 64:.5f}')
    c1, c2 = 2 * (13 / 56) ** 2, 2 * (13 / 56) ** 2 * 7 / 8
    check('Hoeffding exponents 2(13/56)^2 and its 7/8 (research notes, not printed)', abs(c1 - 0.10778) < 5e-6 and c2 >= 0.0943,
          f'{c1:.6f} and {c2:.6f} (notes 0.10778 and 0.094308 >= 0.0943)')
    vals = [((84 * log(n) + 1.05e5) / (100 * (1 + log(n))), n) for n in range(64, 10 ** 6, 2)]
    m = max(vals)
    check('eps^2 (84 log n + 1.05e5) <= 204.2 eps on the range of Theorem 2.6(b) (research notes, not printed)',
          m[1] == 64 and m[0] <= 204.2 + 5e-2, f'maximum {m[0]:.3f} at n = {m[1]}')
    tail = max((2 * log(n) * 2.07 * (n // 8 + 2) * 2.0 ** (-(n // 8) - 1), n) for n in range(64, 100000, 2))
    tot = 2 + 2 * log(3) + 6 + tail[0]
    check('tail mass adds at most 0.35 eps (research notes, not printed)', tail[0] <= 0.35 and tail[0] > 0.34,
          f'largest 2 log n * 2.07 (T+2) 2^(-T-1) = {tail[0]:.4f} at n = {tail[1]}; '
          f'total {tot:.2f} < 11: {tot < 11}')
    # Proposition A.4: the one-step ratio D_s(b) of the supersolution has the closed form
    # J Phi^(c')_s(b)/Phi^c_s(b), and log D_s(b) <= kappa/Sigma_s + 2 kappa/(3 Sigma_s^2) on feasible states.
    def lPhi(n, s, b, c):
        h = n // 2
        out = np.full(b.shape, -np.inf)
        ok = (h - b >= 0) & (h - b <= n - s)
        bb = b[ok]
        out[ok] = (gammaln(n - s + 1) - gammaln(h - bb + 1) - gammaln(n - s - h + bb + 1)
                   + betaln(h + c, h + c) - betaln(bb + c, s - bb + c))
        return out
    worst_gap, worst_exc = 0.0, -np.inf
    for n in (64, 500, 2000):
        h = n // 2
        for eps in (1e-5, 0.01, 0.1, 0.24):
            gam = eps / (1 - 2 * eps)
            kap = 2 * eps / (1 - 4 * eps)
            for s in range(1, n):
                b = np.arange(max(1, s - h), min(h, s - 1) + 1, dtype=float)
                if b.size == 0:
                    continue
                c, cp = kap * (s + 10), kap * (s + 11)
                r = eps + (1 - 2 * eps) * b / s
                l0 = lPhi(n, s, b, c)
                lD = np.logaddexp(np.log1p(-r) + lPhi(n, s + 1, b, cp), np.log(r) + lPhi(n, s + 1, b + 1, cp)) - l0
                d = s / 2 - b
                u, v = d / (s + 2 * cp), d / (n - s)
                rho = (s + 2 * cp) / (s * (1 + 2 * gam))
                lJ = np.log(1 - (rho - 1) * u * (u + v) / (0.25 - u * u)) + lPhi(n, s, b, cp) - l0
                worst_gap = max(worst_gap, float(np.max(np.abs(lD - lJ))))
                Sig = s + 2 * c
                worst_exc = max(worst_exc, float(np.max(lD - kap / Sig - 2 * kap / (3 * Sig ** 2))))
    check('closed form of the one-step ratio D_s(b) (Proposition A.4(a))', worst_gap < 1e-9,
          f'largest difference of logs {worst_gap:.1e}, n = 64, 500, 2000 and 4 values of eps')
    check('log D_s(b) <= kappa/Sigma_s + 2 kappa/(3 Sigma_s^2) on every feasible state (Proposition A.4)', worst_exc <= 1e-12,
          f'largest excess {worst_exc:.2e}')
    # Research notes behind Remark 2.9 (not printed): the explicit bounds on the bridge sums A_t and B_t, and the closed form
    # of the second moment E(u - 2 b_u)^2 under the bridge.
    ok_a = ok_b = ok_m = True
    for n in (64, 256, 1000):
        h = n // 2
        Hn1 = sum(1.0 / j for j in range(1, n))
        for t in range(1, (n + 2) // 4 + 1):
            A, B = bridge_A(n, t)
            ok_a &= A >= 2 * (Hn1 - sum(1.0 / j for j in range(1, t + 1)) - 1 - 1 / t) - 1e-12
            if t <= n / 8:
                ok_b &= B <= 84 * (t + 1 + log(n)) + 683 * (t + 1) ** 3 + 19100
        for t in (1, 3, 7):
            P = np.zeros(h + 2)
            P[1] = 1.0
            for u in range(t + 1, n):
                lo, hi = max(1, u - h), min(h, u - t)
                b = np.arange(lo, hi + 1, dtype=float)
                m2 = float(np.dot(P[lo:hi + 1], (u - 2 * b) ** 2))
                exact = ((t - 1) ** 2 * (n - u) ** 2 / (n - t - 1) ** 2
                         + 4.0 * (u - t - 1) * (h - 1) * (h - t) * (n - u) / ((n - t - 1) ** 2 * (n - t - 2)))
                ok_m &= abs(m2 - exact) <= 1e-9 * max(1.0, exact)
                pr = (h - b) / (n - u)
                seg = P[lo:hi + 1].copy()
                P[lo:hi + 1] = seg * (1 - pr)
                P[lo + 1:hi + 2] += seg * pr
                P[:lo] = 0.0
    check('A_t >= 2(H_(n-1) - H_t - 1 - 1/t) for t <= (n+2)/4 (research notes, not printed)', ok_a, 'n = 64, 256, 1000')
    check('B_t <= 84(t+1+log n) + 683(t+1)^3 + 19100 for t <= n/8 (research notes, not printed)', ok_b, 'n = 64, 256, 1000')
    check('closed form of E(u - 2 b_u)^2 under the bridge (research notes, not printed)', ok_m, 'n = 64, 256, 1000 and t = 1, 3, 7, every u')
    # Research notes (not printed): the hypothesis eps(1+log n) <= 1/100 of Theorem 2.6(b) holds on x <= 2 Lambda_n from n >= 6e4.
    def hyp(n):
        L = 2 * log(n) - log(8)
        return 2 * L / n * (1 + log(n)) <= 0.01
    first = next(n for n in range(1000, 200000, 2) if hyp(n) and all(hyp(m) for m in range(n, n + 2000, 2)))
    check('hypothesis of Theorem 2.6(b) holds on x <= 2 Lambda_n for every n >= 6e4 (research notes, not printed)', first <= 6e4,
          f'it holds from n = {first} on')


# ---------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--full', action='store_true', help='also run the second method on the largest cells')
    args = ap.parse_args()
    T0 = time.time()
    print('Paper D, Section 2: the elephant walk and its crossing' + (' (full run)' if args.full else ' (quick run)'))
    exact_checks()
    proof_constants()

    # ------------------------------------------------ Proposition 2.3 on small n, exactly
    print('\nProposition 2.3 (monotone likelihood ratio), exact check', flush=True)
    ok = True
    for n in range(2, 13):
        grid = [Fraction(k, 20) for k in range(1, 20)]
        prev = None
        for e in grid:
            law = [Fraction(0)] * (n + 1)
            law[0] = Fraction(1)
            for t in range(1, n):
                new = [Fraction(0)] * (n + 1)
                for b in range(t):
                    if law[b]:
                        r = e + (1 - 2 * e) * Fraction(b, t)
                        new[b] += law[b] * (1 - r)
                        new[b + 1] += law[b] * r
                law = new
            ratios = [law[k] / law[0] for k in range(1, n)]
            if prev is not None:
                ok &= all(a > b for a, b in zip(ratios, prev))
            if e >= Fraction(1, 2) and n % 2 == 0:
                ok &= law[n // 2] >= law[0]            # C_n >= 2 E_n, and 2E_n = P_+(M_n = 0)
            prev = ratios
    check('P_+(M_n = k)/P_+(M_n = 0) strictly increasing in eps, 2 <= n <= 12', ok,
          'exact rationals on eps = 1/20, ..., 19/20; also C_n >= 2E_n for eps >= 1/2')

    # ------------------------------------------------ crossings
    print('\nCrossings of the elephant walk (Table 1, Theorem 2.7)', flush=True)
    grid = [50, 100, 200, 400, 800, 1600, 3200, 6400, 12800] + ([25600] if args.full else []) + [51200]
    table = {50: ('3.940487', '4.288636', '+0.3452', '1.007'),
             400: ('7.629217', '7.843768', '+0.0621', '1.273'),
             1600: ('10.240565', '10.340051', '+0.0179', '1.388'),
             3200: ('11.546834', '11.610464', '+0.0097', '1.431'),
             12800: ('14.158845', '14.182921', '+0.0028', '1.497'),
             51200: ('16.778468', '16.786946', '+0.0008', '1.547')}
    # the 10-decimal values of the research notes (not printed), checked as well
    notes10 = {50: '3.9404868665', 400: '7.6292168962', 1600: '10.2405649147', 3200: '11.5468344808',
               12800: '14.1588452626', 51200: '16.7784677365'}
    recorded = {100: '5.0958966738', 200: '6.3405901682', 800: '8.9334617102',
             6400: '12.8524830457', 25600: '15.4672095164'}
    X = {}
    for n in grid:
        t0 = time.time()
        xa = crossing_A(n)
        vals = {'A': xa}
        if n <= 12800 or args.full:
            vals['B'] = crossing_B(n)
        X[n] = xa
        dt = time.time() - t0
        if n in table:
            agree(f'x_{n} (Table 1)', table[n][0], vals, f'  [{dt:.1f}s]')
            agree(f'x_{n} to 10 decimals (research notes, not printed)', notes10[n], vals)
        else:
            agree(f'x_{n} (research notes, not printed)', recorded[n], vals, f'  [{dt:.1f}s]')
        check(f'x_{n} >= 2(1 - eps_{n}) (hypothesis of Corollary 3.6; the text after it proves this for even n >= 1688)', xa >= 2 * (1 - xa / n), f'{xa:.4f}')
        if n in table:
            g1, g2 = g_root(n), g_lambert(n)
            agree(f'g_{n}', table[n][1], {'root finder': g1, 'Lambert W': g2})
            agree(f'x_{n} - x_2nd', table[n][2], {'A': xa - x_second(n)})
            agree(f'x_{n}/log n', table[n][3], {'A': xa / log(n)})
        check(f'0 < g_{n} - x_{n}', 0 < g_root(n) - xa, f'{g_root(n) - xa:.4f}')
    for n, pr in ((3200, '1.43'), (12800, '1.50'), (51200, '1.55')):
        if n in X:
            agree(f'x_{n}/log n (research notes, not printed)', pr, {'A': X[n] / log(n)})
    if not args.full:
        print('  skip  method B at n = 51200 (run with --full)')

    # ------------------------------------------------ bounds at the crossing
    print('\nBridge bound J_n and upper bound U_n at the crossing (research notes, not printed)', flush=True)
    bounds = {50: ('0.915', '69.5'), 400: ('0.9905', '1.770'), 1600: ('0.99868', '1.188'),
              3200: ('0.99954', '1.0996'), 12800: ('0.99995', '1.0289')}
    for n, (jp, up) in bounds.items():
        if n == 12800 and not args.full:
            print('  skip  J_12800/C_12800 = 0.99995 and U_12800/C_12800 = 1.0289 (run with --full)')
            continue
        t0 = time.time()
        x = X[n]
        eps = x / n
        C = center_window(n, eps)
        T = min(n // 2, 60)
        ABa = {t: bridge_A(n, t) for t in range(1, T + 1)}
        jv = {'A': jensen(n, eps, ABa) / C}
        if n <= 1600 or args.full:
            ABb = {t: bridge_B(n, t) for t in range(1, T + 1)}
            jv['B'] = jensen(n, eps, ABb) / C
        agree(f'J_{n}/C_{n} (research notes, not printed)', jp, jv, f'  [{time.time() - t0:.1f}s]')
        agree(f'U_{n}/C_{n} (research notes, not printed)', up, {'A': upper_A(n, eps) / C, 'B': upper_B(n, eps) / C})

    # ------------------------------------------------ Markov comparison
    print('\nComparison with the Markov walk (Theorem 2.8)', flush=True)
    paperA = {50: 0.94200405, 100: 0.96496633, 200: 0.97939018, 400: 0.98812464}
    worst = 0.0
    for N, pv in paperA.items():
        worst = max(worst, abs(z_runcount(N)[1] - pv), abs(z_dp(N)[1] - pv))
    check('Markov crossings p_50, p_100, p_200, p_400 of Paper A', worst < 5e-9,
          f'run-count formula and DP both within {worst:.1e} of Paper A table')
    cstar = 0.5 * log(2 * pi) - 0.25
    agree('c_* = log(2 pi)/2 - 1/4', '0.668939', {'formula': cstar})
    Dnotes = {50: '-0.02123', 400: '-0.03319', 1600: '+0.02921', 3200: '+0.04786',
              12800: '+0.06416', 51200: '+0.06522'}
    DLpaper = {50: '-0.083', 400: '-0.199', 1600: '+0.215', 3200: '+0.386',
               12800: '+0.607', 51200: '+0.707'}
    D = {}
    for n in X:
        za = z_runcount(n)[0]
        vals = {'A': X[n] - (2 * za - log(2 * pi))}
        if n <= 12800 or args.full:
            zb = z_dp(n)[0]
            vals['B'] = X[n] - (2 * zb - log(2 * pi))
        D[n] = vals['A']
        if n in Dnotes:
            agree(f'D({n}) (research notes, not printed)', Dnotes[n], vals)
            agree(f'D({n}) log n (Table 1)', DLpaper[n], {k: v * log(n) for k, v in vals.items()})
    neg = [n for n in D if n <= 400]
    check('D(n) < 0 for n <= 400 and D(800) > 0 (sign change between 400 and 800, text after Theorem 2.8)',
          all(D[n] < 0 for n in neg) and D[800] > 0,
          ', '.join(f'D({n}) = {D[n]:+.5f}' for n in sorted(D) if n <= 1600))
    agree('c_* = 0.669 (text after Theorem 2.8)', '0.669', {'formula': cstar})
    if 51200 in D:
        agree('D(51200) log 51200 = 0.707 (text after Theorem 2.8)', '0.707', {'A': D[51200] * log(51200)})
    for n, dp, cp in ((3200, '0.0479', '0.083'), (12800, '0.0642', '0.071'), (51200, '0.0652', '0.062')):
        agree(f'c_*/log {n} (research notes, not printed)', cp, {'formula': cstar / log(n)})
        if n in D:
            agree(f'D({n}) (research notes, not printed)', dp, {'A': D[n]})

    # ------------------------------------------------ second coefficient
    print('\nSecond coefficient (Remark 2.9)', flush=True)
    K2 = 2 * GAMMA - 2 - log(2)
    Ainf = lambda t: 2 * (GAMMA - 1 - log(2)) + (t - 2) * sum(1.0 / j for j in range(1, t))
    series = sum(t * 2.0 ** (-t - 1) * (Ainf(t) - (t - 1)) for t in range(1, 200))
    agree('lim k_2(n) - 2 log n = 2 gamma - 2 - log 2 (Remark 2.9)', '-1.5387158508', {'closed form': K2, 'series over t': series})

    # The closed form of A^oo_t rests on an exact pre-limit identity (research notes, not printed):
    # sum_{m=0}^M e_{m+t+1} equals an explicit expression in harmonic numbers and the
    # integrals I(j,k) = int_0^1 x^j ((1+x)/2)^k dx. We check it in exact rationals.
    def Hq(k):
        return sum((Fraction(1, j) for j in range(1, k + 1)), Fraction(0))

    def Iq(j, k):
        return Fraction(1, 2 ** k) * sum((Fraction(comb(k, i), i + j + 1) for i in range(k + 1)), Fraction(0))

    def e_exact(t, m):
        u = m + t + 1
        return sum((Fraction(comb(m, K), 2 ** m) * Fraction((u - 2 * (1 + K)) ** 2, 2 * (1 + K) * (u - 1 - K))
                    for K in range(m + 1)), Fraction(0))

    def rhs(t, M):
        r = 2 * t * Hq(M + 1) - sum((1 + Fraction(t, m + 1)) * Fraction(1, 2 ** m) for m in range(M + 1))
        if t >= 2:
            r += 1 - Fraction(1, 2 ** (M + 1))
            r -= (t - 1) * sum((Iq(t - 2, k + 1) for k in range(M + 1)), Fraction(0))
        return r - t * (Hq(t - 1) - sum((Iq(j, M + 1) for j in range(t - 1)), Fraction(0)))

    ok = True
    for t in range(1, 7):
        lhs = Fraction(0)
        for M in range(0, 25):
            lhs += e_exact(t, M)
            ok &= (lhs == rhs(t, M))
    check('pre-limit identity behind A^oo_t, t = 1..6, M = 0..24 (research notes, not printed)', ok, 'exact rationals')
    mp.mp.dps = 50
    S, Hk = mp.mpf(0), mp.mpf(0)
    for t in range(1, 600):
        S += t * (t - 2) * mp.mpf(2) ** (-t - 1) * Hk
        Hk += mp.mpf(1) / t
    check('sum_t t(t-2) 2^(-t-1) H_(t-1) = 2 + log 2 (research notes, not printed)', abs(S - 2 - mp.log(2)) < mp.mpf(10) ** -40,
          f'difference {mp.nstr(S - 2 - mp.log(2), 3)}')
    # Second route: A^oo_t from its definition lim_U (sum_{u=t+1}^U e_u - 2 log U), with
    # e_u = E (u-2B)^2/(2B(u-B)), B = 1 + Bin(u-t-1, 1/2), and the tail sum_{u>U} (e_u - 2/u)
    # estimated by a_t sum_{u>U} 1/u^2. The tail estimate limits the accuracy to about 1e-5.
    from scipy.stats import binom
    from scipy.special import polygamma
    worst = 0.0
    for t in (1, 2, 3, 4):
        U0 = 3000
        S = 0.0
        for u in range(t + 1, U0 + 1):
            m = u - t - 1
            k = np.arange(m + 1)
            Bv = 1.0 + k
            S += float(np.dot(binom.pmf(k, m, 0.5), (u - 2 * Bv) ** 2 / (2 * Bv * (u - Bv))))
        a_t = 2 * ((t - 1) ** 2 - t - 1) + 6
        val = S - 2 * sum(1.0 / j for j in range(1, U0 + 1)) + 2 * GAMMA + a_t * float(polygamma(1, U0 + 1))
        worst = max(worst, abs(val - Ainf(t)))
    check('A^oo_t closed form against its limit definition (U = 3000), t = 1..4 (research notes, not printed)', worst < 1e-5,
          f'largest difference {worst:.1e}')

    k2paper = {1600: '-1.585878', 12800: '-1.546572', 51200: '-1.541005'}
    kap = {}
    for n in (1600, 3200, 12800, 51200) + ((25600,) if args.full else ()):
        t0 = time.time()
        ca = taylor_window(n, 3)
        k2a = ca[2] / ca[1]
        kap[n] = (k2a, ca[3] / ca[1] - k2a ** 2 / 2)
        vals = {'A': k2a - 2 * log(n)}
        if n <= 12800 or args.full:
            cb = taylor_symmetric(n, 3)
            vals['B'] = cb[2] / cb[1] - 2 * log(n)
        if n in k2paper:
            agree(f'k_2({n}) - 2 log n (research notes, not printed)', k2paper[n], vals, f'  [{time.time() - t0:.1f}s]')
    if not args.full:
        print('  skip  method B for k_2(51200) (run with --full)')
    # Research notes behind Remark 2.9 (not printed): k_2(n) = sum_t w_t [A_t - (t-1)] through the bridge sums.
    n = 400
    h = n // 2
    tot = 0.0
    for t in range(1, 121):
        A, _ = bridge_A(n, t)
        tot += exp(log_pi(n, t)) / (4 / (n + 2)) * (A - (t - 1))
    c = taylor_window(n, 2)
    check('bridge formula for k_2 at n = 400, bridge sum (t <= 120) against the Taylor DP (research notes, not printed)', abs(tot - c[2] / c[1]) < 1e-8,
          f'{tot:.10f} and {c[2] / c[1]:.10f}')

    # ------------------------------------------------ Remark 2.9, refined crossing
    print('\nRefined crossing equation (Remark 2.9, numerical)', flush=True)
    misses = {3200: 5.3e-7, 12800: 1.4e-8, 51200: 3.6e-10}     # Remark 2.9 quotes 3.6e-10. The other values are research notes.
    for n in sorted(kap):
        if n in X and n in misses:
            miss = X[n] - x_refined(n, *kap[n])
            ok = abs(miss - misses[n]) <= 0.06 * misses[n]
            check(f'x_{n} minus the refined root with k_2, k_3 (n = 51200, a research check not quoted in the paper, research notes otherwise)', ok, f'{miss:+.2e} (recorded {misses[n]:.1e})')
        if n in X:
            # The research notes prove x_n <= xhat_n + O((log n)^3/n^2), with xhat_n the root with k_2 only (not printed).
            # The O term is not small at these n, so we only check that the scaled excess stays bounded.
            one = x_refined(n, kap[n][0], 0.0)
            sc = (X[n] - one) * n * n / log(n) ** 3
            check(f'(x_{n} - xhat_{n}) n^2/(log n)^3 stays bounded (research notes, not printed)', sc < 3,
                  f'x_n - xhat_n = {X[n] - one:+.2e}, scaled {sc:.2f}')

    print(f'\nSection 2 checks done in {time.time() - T0:.0f}s: '
          + ('all passed.' if not FAILS else f'{len(FAILS)} FAILED: ' + '; '.join(FAILS)))
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
