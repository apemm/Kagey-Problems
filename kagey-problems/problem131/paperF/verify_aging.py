"""Checks for Section 5 and the aging appendix of Paper D (the aging walk).

Model. X_1 is +1 or -1 with probability 1/2. For k >= 2 the walk switches
direction with probability c/k (0 < c < 2) and keeps it otherwise. A_n is the
number of +1 steps. For even n, c_n is the value of c with P(A_n = n/2) = P(A_n = n).

Method A. Forward recursion on (A_k, X_k) in double precision, with nonnegative
terms only.
Method B. The generating function E z^(A_n) as a product of 2 x 2 transfer
matrices at the (n+1)-th roots of unity, then an inverse discrete Fourier transform.
Method C. The path-weight form: P(A_n = s)/P(A_n = n) is a sum over paths of
products of the odds w_t = c/(t-c), computed in double precision, and in exact
rationals or 30-digit arithmetic where noted.

Run with python -B verify_aging.py, or add --full for the second method on every
even n <= 1000 and for n = 6400 by both methods. Checks of numbers from the research notes
that the paper does not print are kept, labeled 'research notes, not printed'.

The d-state chain of Theorem 5.2 starts in state 1 and at step k >= 2 moves to each of the
other d-1 states with probability theta/(k+d-2). Its joint law of (visit counts, last state)
is computed in exact rationals by a forward recursion and by enumerating all paths.
"""
import argparse
import sys
import time
from fractions import Fraction
from itertools import product
from math import comb, lgamma, log

import mpmath as mp
import numpy as np
from scipy.optimize import brentq

GAMMA = 0.5772156649015329
FAILS = []


def note(text):
    print('  note  ' + text, flush=True)


def check(label, ok, detail):
    print(('  ok    ' if ok else '  FAIL  ') + label + ': ' + detail, flush=True)
    if not ok:
        FAILS.append(label)


def tol_of(printed):
    s = printed.lstrip('+-')
    mant = s.split('e')[0]
    exp10 = int(s.split('e')[1]) if 'e' in s else 0
    dec = len(mant.split('.')[1]) if '.' in mant else 0
    return 0.5 * 10.0 ** (exp10 - dec) * (1 + 1e-9) + 1e-15


def agree(label, printed, values, extra=''):
    target = float(printed)
    t = tol_of(printed)
    ok = all(abs(v - target) <= t for v in values.values())
    shown = ', '.join(f'{k} {v:.12g}' for k, v in values.items())
    check(label, ok, f'paper {printed}; {shown}{extra}')


# ---------------------------------------------------------------- laws

def law_A(n, c):
    """P(A_n = s), s = 0..n, forward recursion on (A_k, X_k)."""
    A = np.zeros(n + 1)
    B = np.zeros(n + 1)
    A[1] = 0.5
    B[0] = 0.5
    for k in range(2, n + 1):
        p = c / k
        nA = np.zeros(n + 1)
        nB = np.zeros(n + 1)
        nA[1:k + 1] = (1 - p) * A[0:k] + p * B[0:k]
        nB[0:k] = p * A[0:k] + (1 - p) * B[0:k]
        A, B = nA, nB
    return A + B


def law_B(n, c):
    """The same law from the pgf at the (n+1)-th roots of unity."""
    z = np.exp(2j * np.pi * np.arange(n + 1) / (n + 1))
    u = 0.5 * z
    v = 0.5 * np.ones(n + 1, dtype=complex)
    for k in range(2, n + 1):
        p = c / k
        u, v = z * ((1 - p) * u + p * v), p * u + (1 - p) * v
    return (np.fft.fft(u + v) / (n + 1)).real


def ratio_C(n, c):
    """R_(n,s) = P(A_n = s)/P(A_n = n) by the path-weight recursion with odds w_t = c/(t-c)."""
    A = np.zeros(n + 1)
    B = np.zeros(n + 1)
    A[1] = B[0] = 1.0
    for t in range(2, n + 1):
        w = c / (t - c)
        nA = np.zeros(n + 1)
        nB = np.zeros(n + 1)
        nA[1:t + 1] = A[0:t] + w * B[0:t]
        nB[0:t] = w * A[0:t] + B[0:t]
        A, B = nA, nB
    return A + B


def law_frac(n, c, start=None, joint=False):
    """Exact law in rationals; start=+1 fixes X_1 = +1."""
    c = Fraction(c)
    A = [Fraction(0)] * (n + 1)
    B = [Fraction(0)] * (n + 1)
    if start is None:
        A[1] = Fraction(1, 2)
        B[0] = Fraction(1, 2)
    else:
        A[1] = Fraction(1)
    for k in range(2, n + 1):
        p = c / k
        nA = [Fraction(0)] * (n + 1)
        nB = [Fraction(0)] * (n + 1)
        for s in range(k):
            if A[s] or B[s]:
                nA[s + 1] += (1 - p) * A[s] + p * B[s]
                nB[s] += p * A[s] + (1 - p) * B[s]
        A, B = nA, nB
    return (A, B) if joint else [a + b for a, b in zip(A, B)]


def brute(n, c, start=None):
    """Exact law by enumerating all 2^n direction sequences."""
    c = Fraction(c)
    P = [Fraction(0)] * (n + 1)
    for x in product((1, -1), repeat=n):
        if start is not None and x[0] != start:
            continue
        pr = Fraction(1, 2) if start is None else Fraction(1)
        for k in range(2, n + 1):
            pr *= (c / k) if x[k - 1] != x[k - 2] else (1 - c / k)
        P[sum(1 for v in x if v == 1)] += pr
    return P


def dstate_law(d, N, theta):
    """Exact joint law {(counts, last state): probability} of the d-state aging chain after N steps."""
    theta = Fraction(theta)
    law = {((1,) + (0,) * (d - 1), 0): Fraction(1)}
    for k in range(2, N + 1):
        move = theta / (k + d - 2)
        stay = 1 - (d - 1) * move
        assert stay > 0
        new = {}
        for (n, j), pr in law.items():
            for i in range(d):
                m = list(n)
                m[i] += 1
                key = (tuple(m), i)
                new[key] = new.get(key, Fraction(0)) + pr * (stay if i == j else move)
        law = new
    return law


def dstate_brute(d, N, theta):
    """The same joint law by enumerating all d^(N-1) paths that start in state 1."""
    theta = Fraction(theta)
    law = {}
    for tail in product(range(d), repeat=N - 1):
        x = (0,) + tail
        pr = Fraction(1)
        for k in range(2, N + 1):
            move = theta / (k + d - 2)
            pr *= move if x[k - 1] != x[k - 2] else 1 - (d - 1) * move
        key = (tuple(x.count(i) for i in range(d)), x[-1])
        law[key] = law.get(key, Fraction(0)) + pr
    return law


def compositions(N, d):
    """Compositions of N into d nonnegative parts."""
    if d == 1:
        yield (N,)
        return
    for a in range(N + 1):
        for rest in compositions(N - a, d - 1):
            yield (a,) + rest


def log_end(n, c):
    """log P(A_n = n) = log((1/2) rho(1, n)), rho(1, n) = Gamma(n+1-c)/(Gamma(2-c) Gamma(n+1))."""
    return lgamma(n + 1 - c) - log(2.0) - lgamma(2 - c) - lgamma(n + 1)


def crossing(n, method, lo=0.3, hi=0.9999999):
    if method == 'A':
        F = lambda c: log(law_A(n, c)[n // 2]) - log_end(n, c)
    elif method == 'B':
        F = lambda c: log(law_B(n, c)[n // 2]) - log_end(n, c)
    else:
        F = lambda c: log(ratio_C(n, c)[n // 2])
    return brentq(F, lo, hi, xtol=1e-15, rtol=1e-15, maxiter=200)


def c_N(N):
    """c^(N): the root in (0, 1) of N rho(1, N) = 2c."""
    h = lambda c: log(N) + lgamma(N + 1 - c) - lgamma(2 - c) - lgamma(N + 1) - log(2 * c)
    return brentq(h, 1e-6, 0.9999999, xtol=1e-15)


def shape_ok(P, n):
    """Center the unique interior minimum, profile increasing from n/2 to n-1, argmax in {1, n-1}."""
    m = n // 2
    inner = P[1:n]
    uniq = int(np.argmin(inner)) + 1 == m and np.sum(inner <= P[m] * (1 + 1e-12)) == 1
    incr = bool(np.all(np.diff(P[m:n]) > 0))
    return uniq and incr and int(np.argmax(P)) in (1, n - 1)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--full', action='store_true', help='also run the heavy cells')
    args = ap.parse_args()
    T0 = time.time()
    print('Paper D, Section 5: the aging walk' + (' (full run)' if args.full else ' (quick run)'))

    # ------------------------------------------------ exact laws at c = 1
    print('\nThe law at c = 1 (Section 5), exact rationals', flush=True)
    ok = True
    for n in range(2, 61):
        A, B = law_frac(n, 1, start=+1, joint=True)
        ok &= A[n] == Fraction(1, n) and B[n] == 0 and A[0] == B[0] == 0
        for s in range(1, n):
            ok &= A[s] == Fraction(s - 1, n * (n - 1)) and B[s] == Fraction(n - s, n * (n - 1))
        P = law_frac(n, 1)
        ok &= P[0] == P[n] == Fraction(1, 2 * n) and all(P[s] == Fraction(1, n) for s in range(1, n))
    check('given X_1 = +1 and c = 1: joint law (s-1)/(n(n-1)), (n-s)/(n(n-1)), and A_n uniform on {1..n}; '
          'fair start: ends 1/(2n), interior 1/n', ok, 'every 2 <= n <= 60')
    ok = True
    for n in range(2, 13):
        ok &= brute(n, 1, start=+1)[1:] == [Fraction(1, n)] * n and brute(n, 1) == law_frac(n, 1)
        for c in (Fraction(1, 3), Fraction(7, 10), Fraction(3, 2)):
            ok &= brute(n, c) == law_frac(n, c)
    check('brute force over all 2^n paths equals the recursion', ok, 'n <= 12, c in {1/3, 7/10, 1, 3/2}')

    # ------------------------------------------------ monotonicity in c
    print('\nMonotone ratios in c (Section 5)', flush=True)
    ok = True
    grid = [Fraction(k, 10) for k in range(1, 20)]
    for n in range(2, 13):
        prevp = prevf = None
        for c in grid:
            Pp = law_frac(n, c, start=+1)
            Pf = law_frac(n, c)
            rp = [Pp[s] / Pp[n] for s in range(1, n)]
            rf = [Pf[s] / Pf[n] for s in range(1, n)]
            if prevp is not None:
                ok &= all(a > b for a, b in zip(rp, prevp)) and all(a > b for a, b in zip(rf, prevf))
            if c == 1:
                ok &= all(v == 1 for v in rp)
            prevp, prevf = rp, rf
    check('P(A_n = s)/P(A_n = n) strictly increasing in c for 1 <= s <= n-1 (fixed and fair start), '
          'and equal to 1 at c = 1 for the fixed start', ok, 'exact, n <= 12, c = 0.1, ..., 1.9')

    # ------------------------------------------------ d states (Theorem 5.2)
    print('\nThe d-state chain (Theorem 5.2), exact rationals', flush=True)
    ok, nbins = True, 0
    for d in (2, 3, 4):
        for N in range(2, 9):
            law = dstate_law(d, N, 1)
            bins = [n for n in compositions(N, d) if n[0] >= 1]
            ok &= len(bins) == comb(N + d - 2, d - 1) and sum(law.values()) == 1
            den = (N - 1) * comb(N + d - 2, d - 1)
            for n in bins:
                nbins += 1
                for j in range(d):
                    ok &= law.get((n, j), Fraction(0)) == Fraction(n[j] - (1 if j == 0 else 0), den)
                ok &= sum(law.get((n, j), Fraction(0)) for j in range(d)) == Fraction(1, comb(N + d - 2, d - 1))
            ok &= all(n[0] >= 1 for n, _ in law)
    check('theta = 1: P(counts = n, X_N = j) = (n_j - 1{j=1})/((N-1) binom(N+d-2, d-1)), counts uniform on the bins',
          ok, f'd = 2, 3, 4 and 2 <= N <= 8 ({nbins} bins)')
    ok = True
    for d in (2, 3, 4):
        for N in range(2, 6 if d == 4 else 7):
            for th in (1, Fraction(9, 10), Fraction(11, 10)):
                ok &= dstate_law(d, N, th) == {k: v for k, v in dstate_brute(d, N, th).items() if v}
    check('the recursion equals brute force over all paths', ok, 'd = 2, 3 (N <= 6), d = 4 (N <= 5), theta in {9/10, 1, 11/10}')
    ok = True
    grid = [Fraction(1, 2), Fraction(9, 10), Fraction(1), Fraction(11, 10), Fraction(5, 4)]
    for d in (2, 3, 4):
        for N in range(2, 9):
            corner = (N,) + (0,) * (d - 1)
            prev = None
            for th in grid:
                law = dstate_law(d, N, th)
                marg = {}
                for (n, j), pr in law.items():
                    marg[n] = marg.get(n, Fraction(0)) + pr
                ratios = {n: marg[n] / marg[corner] for n in marg if n != corner}
                if th < 1:
                    ok &= all(v < 1 for v in ratios.values())
                elif th == 1:
                    ok &= all(v == 1 for v in ratios.values())
                else:
                    ok &= all(v > 1 for v in ratios.values())
                if prev is not None:
                    ok &= all(ratios[n] > prev[n] for n in ratios)
                prev = ratios
    check('P(n)/P(N e_1) < 1 at theta = 0.9, = 1 at theta = 1, > 1 at theta = 1.1, and strictly increasing '
          'along theta = 1/2, 9/10, 1, 11/10, 5/4, for every bin n other than the corner', ok,
          'exact, d = 2, 3, 4 and 2 <= N <= 8')
    ok = True
    for N in range(2, 9):
        law = dstate_law(2, N, 1)
        A, B = law_frac(N, 1, start=+1, joint=True)
        for s in range(1, N + 1):
            ok &= law.get(((s, N - s), 0), Fraction(0)) == A[s] and law.get(((s, N - s), 1), Fraction(0)) == B[s]
    check('d = 2 is the two-state walk with c = theta', ok, '2 <= N <= 8')

    # ------------------------------------------------ c^(N) and the bracket
    print('\nThe bracket c^(n/2+1) <= c_n <= c^(n) and the first-order crossing (aging appendix)', flush=True)
    cs = [c_N(N) for N in range(3, 3001)]
    check('c^(N) increases in N and stays below 1 (aging appendix)', all(a < b < 1 for a, b in zip(cs, cs[1:])), 'N = 3..3000')
    # For large N the difference lgamma(N+1-c) - lgamma(N+1) cancels badly in double precision,
    # so here the root is found in 40-digit arithmetic.
    mp.mp.dps = 40
    rows = []
    for N in (10 ** 2, 10 ** 4, 10 ** 6, 10 ** 8, 10 ** 12, 10 ** 20):
        f = lambda c: (mp.log(N) + mp.loggamma(N + 1 - c) - mp.loggamma(2 - c) - mp.loggamma(N + 1)
                       - mp.log(2 * c))
        e = 1 - mp.findroot(f, (mp.mpf('0.3'), mp.mpf('0.9999999999')), solver='anderson')
        L = mp.log(N)
        rows.append((N, e, float((e - mp.log(2) / (L + 1 + mp.euler)) * L ** 3)))
    lim = float((mp.pi ** 2 / 6 - 1) * mp.log(2) ** 2 / 2)
    check('1 - c^(N) = log 2/(log N + 1 + gamma) + O((log N)^(-3)) (aging appendix)', max(abs(r[2]) for r in rows) < 0.2,
          '(remainder) (log N)^3 = ' + ', '.join(f'{r[2]:+.3f} at N = {r[0]:.0e}' for r in rows)
          + f'; the next term predicts the limit (pi^2/6 - 1)(log 2)^2/2 = {lim:.3f}')

    c3 = c_N(3)
    check('kappa_J = c/(1+c) at c = c^(3) is at least 0.42 > 0.4 (aging appendix)', c3 / (1 + c3) >= 0.42,
          f'c^(3) = {c3:.6f}, kappa_J = {c3 / (1 + c3):.4f}')
    # Aging appendix: c/n <= C_n <= lambda_(h+1,n) = c/(h+1) rho(h+1, n) for c < 1.
    ok = True
    for n in (10, 50, 200, 800):
        h = n // 2
        for c in (0.2, 0.5, 0.8, 0.95):
            Cn = law_A(n, c)[h]
            lam = c / (h + 1) * np.exp(lgamma(n + 1 - c) - lgamma(h + 2 - c) + lgamma(h + 2) - lgamma(n + 1))
            ok &= c / n <= Cn <= lam
    check('c/n <= C_n <= c/(h+1) rho(h+1, n) for c < 1 (aging appendix)', ok, 'n = 10, 50, 200, 800 and c = 0.2, 0.5, 0.8, 0.95')

    # ------------------------------------------------ Theta(c)
    print('\nThe function Theta(c) = log(2 Gamma(2-c) d_c), d_c = 4^(1-c)/B(c, c) (aging appendix)', flush=True)
    mp.mp.dps = 30
    Theta = lambda c: mp.log(2 * mp.gamma(2 - c) * mp.power(4, 1 - c) / mp.beta(c, c))
    agree('Theta(1) = log 2 (constant of the expansion of c_n in Section 5)', '0.6931471806', {'formula': float(Theta(mp.mpf(1)))})
    d1 = mp.diff(Theta, 1)
    d1b = -mp.digamma(1) - mp.log(4) - 2 * mp.digamma(1) + 2 * mp.digamma(2)
    agree("Theta'(1) = gamma + 2 - 2 log 2 (constant of the expansion of c_n in Section 5)", str(round(GAMMA + 2 - 2 * log(2), 10)),
          {'numerical derivative': float(d1), 'digamma formula': float(d1b)})

    # Local limit at the center (aging appendix): N C_N -> d_c = 4^(1-c)/B(c, c).
    ok, shown = True, []
    for c in (0.75, 0.9, 1.0, 1.3):
        dc = float(mp.power(4, 1 - c) / mp.beta(c, c))
        errs = [abs(n * law_A(n, c)[n // 2] - dc) for n in (400, 1600, 6400)]
        ok &= errs[2] < 2e-3 and (c == 1.0 or errs[0] > errs[1] > errs[2])
        shown.append(f'c = {c}: ' + ', '.join(f'{e:.1e}' for e in errs))
    check('|N C_N - d_c| is small and decreases along N = 400, 1600, 6400 (aging appendix)', ok, '; '.join(shown))

    # ------------------------------------------------ crossings
    print('\nThe crossing c_n (Section 5)', flush=True)
    X = {}
    for n, printed, hp in ((200, '0.8925', 0.892525269532), (800, '0.9116', 0.911589002819)):
        t0 = time.time()
        ca, cb, cc = crossing(n, 'A'), crossing(n, 'B'), crossing(n, 'C')
        X[n] = ca
        agree(f'c_{n}' + (' (Section 5)' if n == 200 else ' (aging appendix)'), printed,
              {'A': ca, 'B': cb, 'C': cc}, f'  [{time.time() - t0:.1f}s]')
        check(f'c_{n} against the recorded 12-digit value', max(abs(v - hp) for v in (ca, cb, cc)) < 1e-11,
              f'{hp} (A, B, C within {max(abs(v - hp) for v in (ca, cb, cc)):.1e})')
        lo, hi = c_N(n // 2 + 1), c_N(n)
        check(f'c^({n // 2 + 1}) <= c_{n} <= c^({n}) (aging appendix)', lo <= ca <= hi, f'[{lo:.9f}, {hi:.9f}]')
    agree('c_200 to 5 digits (aging appendix)', '0.89253', {'A': X[200]})
    L = log(200)
    M = L + GAMMA + 2 - 2 * log(2)
    one = 1 - log(2) / M
    agree('first 2 terms of the expansion of c_n at n = 200 (Section 5)', '0.8932', {'formula': one})
    g2 = mp.pi ** 2 / 2 - 4
    two = one - float(g2 / 2) * log(2) ** 2 / M ** 3
    agree('two-term value at n = 200 (with the (g_2/2)(log 2)^2/M^3 term) (aging appendix)', '0.89236', {'formula': two})
    note(f'the expansion 1 - log 2/(log n + gamma + 2 - 2 log 2) alone gives {one:.5f} at n = 200; '
         f'0.89236 also contains the M^(-3) term {two - one:+.5f}')
    ok = True
    for n in range(4, 401, 2):
        c = crossing(n, 'A', c_N(n // 2 + 1) - 1e-9, c_N(n) + 1e-9)
        ok &= c_N(n // 2 + 1) <= c <= c_N(n) and c < 1
    check('c^(n/2+1) <= c_n <= c^(n) < 1 for every even 4 <= n <= 400 (aging appendix)', ok, 'method A')
    t0 = time.time()
    c = Fraction(X[200]).limit_denominator(10 ** 9)
    signs = []
    for dc in (Fraction(-1, 10 ** 6), Fraction(1, 10 ** 6)):
        P = law_frac(200, c + dc)
        signs.append((P[100] > P[200]) - (P[100] < P[200]))
    check('exact rational sign check at c_200 -+ 1e-6 (Section 5)', signs == [-1, 1],
          f'sign of P(center) - P(end): {signs}  [{time.time() - t0:.0f}s]')

    # ------------------------------------------------ shape at the crossing
    print('\nShape of the law at c_n (research notes, not printed)', flush=True)
    t0 = time.time()
    bad, badB, prev, nB = [], [], None, 0
    for n in range(4, 1001, 2):
        lo, hi = c_N(n // 2 + 1) - 1e-9, c_N(n) + 1e-9
        c = crossing(n, 'A', lo, hi)
        if not shape_ok(law_A(n, c), n):
            bad.append(n)
        if args.full or n % 20 == 0 or n <= 40:
            nB += 1
            cB = crossing(n, 'B', lo, hi)
            if abs(cB - c) > 1e-11 or not shape_ok(law_B(n, cB), n):
                badB.append(n)
    check('every even 4 <= n <= 1000: center the unique interior minimum, bins 1 and n-1 the largest (research notes, not printed)',
          not bad and not badB, f'A failures {bad}; B checked on {nB} values of n, failures {badB}  [{time.time() - t0:.0f}s]')
    for n in (1600, 3200, 6400):
        t0 = time.time()
        lo, hi = c_N(n // 2 + 1) - 1e-9, c_N(n) + 1e-9
        c = crossing(n, 'A', lo, hi)
        ok = shape_ok(law_A(n, c), n)
        detail = f'c_n = {c:.10f} (A)'
        if n <= 3200 or args.full:
            cB = crossing(n, 'B', lo, hi)
            ok &= abs(cB - c) < 1e-11 and shape_ok(law_B(n, cB), n)
            detail += f', {cB:.10f} (B)'
        check(f'n = {n}: same shape at c_n (research notes, not printed)', ok, detail + f'  [{time.time() - t0:.1f}s]')

    print(f'\nAging checks done in {time.time() - T0:.0f}s: '
          + ('all passed.' if not FAILS else f'{len(FAILS)} FAILED: ' + '; '.join(FAILS)))
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
