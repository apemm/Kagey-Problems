"""Checks for Section 3 and Appendix B of Paper D (the elephant walk near its crossing).

Notation as in the paper. Given X_1 = +1, M_n is the number of steps that differ
from X_1 and f_n(m) = P_+(M_n = m). Then P(A_n = n-m) = (f_n(m) + f_n(n-m))/2.
CP_n is the compound Poisson law with jumps d = 1, ..., n-1 at rates x/(d(d+1)),
and f_L is the Landau density with int e^(-u y) f_L(y) dy = u^u.

Method A. The chain M_t on states 0..t (or truncated at a level, which is exact
below that level because M_t never decreases). CP_n by the Panjer recursion.
The Landau density by the real integral (1/pi) int_0^oo e^(-t log t - l t) sin(pi t) dt.
Method B. The law of A_t with the symmetric start, computed directly (at
n = 10^5 and 10^6, where only small m are needed, the truncated chain written
as a pull recursion). CP_n by the fast Fourier transform of its characteristic
function. The Landau density by Fourier inversion of exp(-i t log t - pi t/2).

Run with python -B verify_elephant_shape.py, or add --full for n = 25600 and
for the second method at n = 10^6. Checks of numbers from the research notes that the paper
no longer prints are kept, labeled 'research notes, not printed'.
"""
import argparse
import sys
import time
from fractions import Fraction
from math import ceil, comb, exp, floor, log, log1p, pi, e as E_CONST

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
    shown = ', '.join(f'{k} {v:.10g}' for k, v in values.items())
    check(label, ok, f'paper {printed}; {shown}{extra}')


# ---------------------------------------------------------------- laws

def law_A(n, eps):
    """P(A_n = a), a = 0..n, from the chain M_t given X_1 = +1 (method A)."""
    p = np.zeros(n + 1)
    p[0] = 1.0
    for t in range(1, n):
        b = np.arange(t, dtype=float)
        r = eps + (1.0 - 2.0 * eps) * b / t
        seg = p[:t].copy()
        p[:t] = seg * (1.0 - r)
        p[1:t + 1] += seg * r
    # p[m] = f_n(m) = P_+(A_n = n-m). Symmetrize.
    return 0.5 * (p[::-1] + p), p


def law_B(n, eps, start='sym'):
    """P(A_n = a) directly (method B). start='sym' is the symmetric start and
    start='plus' fixes X_1 = +1, so that f_n(m) is entry n-m."""
    P = np.zeros(n + 1)
    if start == 'sym':
        P[0] = P[1] = 0.5
    else:
        P[1] = 1.0
    for k in range(1, n):
        a = np.arange(0, k + 1, dtype=float)
        up = (1 - eps) * a / k + eps * (k - a) / k
        Q = np.zeros(n + 1)
        Q[0:k + 1] = P[0:k + 1] * (1 - up)
        Q[1:k + 2] += P[0:k + 1] * up
        P = Q
    return P


def chain_A(n, eps, c0, M):
    """Law of the chain C_1 = c0, C_(k+1) = C_k + Bern(eps + (1-2eps) C_k/k), values 0..M.
    c0 = 0 gives f_n(m); c0 = 1 gives f_n(n-m) at index m. Mass above M is dropped."""
    p = np.zeros(M + 1)
    p[c0] = 1.0
    a = np.arange(M + 1, dtype=float)
    for k in range(1, n):
        L = min(k + 1, M + 1)
        up = eps + (1.0 - 2.0 * eps) * a[:L] / k
        move = p[:L] * up
        p[:L] -= move
        if L < M + 1:
            p[1:L + 1] += move
        else:
            p[1:L] += move[:-1]
    return p


def chain_B(n, eps, c0, M):
    """The same truncated chain written as a 'pull' recursion (new[c] from p[c] and p[c-1])."""
    p = np.zeros(M + 1)
    p[c0] = 1.0
    c = np.arange(M + 1, dtype=float)
    q = 1.0 - 2.0 * eps
    for k in range(1, n):
        b = np.minimum(eps + q * c / k, 1.0)
        new = p * (1.0 - b)
        new[1:] += p[:-1] * b[:-1]
        p = new
    return p


def cp_panjer(x, n, M):
    """CP_n on 0..M by the Panjer recursion m p(m) = x sum_d p(m-d)/(d+1)."""
    p = np.zeros(M + 1)
    p[0] = exp(-x * (1.0 - 1.0 / n))
    w = 1.0 / (np.arange(1, M + 1) + 1.0)
    if n - 1 < M:
        w[n - 1:] = 0.0
    for m in range(1, M + 1):
        p[m] = x / m * np.dot(p[m - 1::-1][:m], w[:m])
    return p


def cp_fft(x, n, M):
    """CP_n on 0..M by FFT of exp(sum_d a_d (z^d - 1)) on a circle of length >= 4n."""
    L = 1
    while L < 4 * n:
        L *= 2
    a = np.zeros(L)
    d = np.arange(1, n, dtype=float)
    a[1:n] = x / (d * (d + 1.0))
    pmf = np.fft.ifft(np.exp(np.fft.fft(a) - a.sum())).real
    return pmf[:M + 1]


def center_of(P, n):
    """The center bin: h for even n, and (n+1)/2 (equal to (n-1)/2 by symmetry) for odd n."""
    return P[n // 2] if n % 2 == 0 else P[(n + 1) // 2]


def crossing(n, method, lo, hi):
    def f(x):
        P = law_A(n, x / n)[0] if method == 'A' else law_B(n, x / n)
        return log(center_of(P, n)) - log(P[n])
    if f(lo) * f(hi) > 0:                      # warm-start bracket missed; use a wide one
        lo, hi = 0.05, 0.9 * n
    return brentq(f, lo, hi, xtol=1e-11)


def crossing_window(n, lo, hi):
    """Crossing by the window DP of Section 2 (only the center is needed)."""
    h = n // 2

    def center(eps):
        P = np.zeros(h + 2)
        P[0] = 1.0
        for t in range(1, n):
            a, b = max(0, h - (n - t)), min(t - 1, h)
            s = np.arange(a, b + 1, dtype=float)
            r = eps + (1.0 - 2.0 * eps) * s / t
            seg = P[a:b + 1].copy()
            P[a:b + 1] = seg * (1.0 - r)
            P[a + 1:b + 2] += seg * r
            if a > 0:
                P[a - 1] = 0.0
        return P[h]
    return brentq(lambda x: log(center(x / n)) - (log(0.5) + (n - 1) * log1p(-x / n)), lo, hi, xtol=1e-11)


def g_root(n):
    L = 2 * log(n) - log(8)
    return brentq(lambda x: x + log(x) - L, 1e-9, L + 5, xtol=1e-15)


# ---------------------------------------------------------------- shape of a law at its crossing

def shape(P, n):
    """Summary of the symmetric law P at its crossing."""
    a0 = (n + 1) // 2
    ms = n - (a0 + int(np.argmax(P[a0:])))                 # upper-half mode distance m*
    sd = np.zeros(n + 1)
    sd[1:n] = P[:-2] - 2 * P[1:-1] + P[2:]                  # second difference at a = 1..n-1
    open_bad = [a for a in range(2 * ms + 1, n - 2 * ms) if sd[a] <= 0]
    end_bad = [a for a in (2 * ms, n - 2 * ms) if 1 <= a <= n - 1 and sd[a] <= 0]
    d1 = np.sign(np.diff(P))
    nz = d1[d1 != 0]
    changes = int(np.sum(nz[1:] != nz[:-1]))                # sign changes of the first difference
    cen = [n // 2] if n % 2 == 0 else [(n - 1) // 2, (n + 1) // 2]
    unique_min = all(P[a] > P[cen[0]] for a in range(1, n) if a not in cen)
    neg_low = [a for a in range(1, n // 2 + 1) if sd[a] <= 0]
    a1 = neg_low[-1] + 1 if neg_low else 1                  # convexity resumes at a_1
    return dict(ms=ms, open_bad=open_bad, end_bad=end_bad, changes=changes,
                unique_min=unique_min, dip=P[n - 1] > P[n], a1=a1, sd=sd)


# ---------------------------------------------------------------- Landau density

def landau_real(lam, k=0):
    """k-th derivative of f_L at lam from the real integral (method A)."""
    g = lambda t: (-t) ** k * mp.exp(-t * mp.log(t) - lam * t) * mp.sin(mp.pi * t) if t > 0 else mp.mpf(0)
    return mp.quad(g, [0, 1, 2, 4, 8, 16, 32, 64, mp.inf]) / mp.pi


def landau_fourier(lam, k=0):
    """The same by Fourier inversion of phi_L(t) = exp(-i t log t - pi t/2), t > 0 (method B)."""
    def g(t):
        if t == 0:
            return mp.mpf(1) if k == 0 else mp.mpf(0)
        return mp.re((-1j * t) ** k * mp.exp(-1j * lam * t) * mp.exp(-1j * t * mp.log(t) - mp.pi * t / 2))
    return mp.quad(g, mp.linspace(0, 80, 81)) / mp.pi


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--full', action='store_true', help='also run n = 25600 and the second method at n = 10^6')
    args = ap.parse_args()
    T0 = time.time()
    print('Paper D, Section 3: the elephant walk near its crossing' + (' (full run)' if args.full else ' (quick run)'))

    # ------------------------------------------------ Lemma 2.4 and the first-order profile, exactly
    print('\nLemma 2.4 and the first-order term of f_n (Section 3.1, exact rationals)', flush=True)
    ok = True
    for n in range(3, 31):
        for d in range(1, n):
            beta = [Fraction(comb(n - d - 1, v - 2), comb(n - 1, v - 1)) if v - 2 <= n - d - 1 else Fraction(0)
                    for v in range(2, n + 1)]
            ok &= sum(beta) == Fraction(n, d * (d + 1))
            ok &= sum((v - 2) * b for v, b in zip(range(2, n + 1), beta)) == Fraction(2 * n * (n - d - 1), d * (d + 1) * (d + 2))
    check('sum_v beta_v(d) = n/(d(d+1)) and sum_v (v-2) beta_v(d) = 2n(n-d-1)/(d(d+1)(d+2)), n <= 30 (Lemma 2.4)', ok, 'exact')
    # Brute force over all recursive trees on [n] for small n: law of the subtree size of v.
    from itertools import product as iproduct
    ok = True
    for n in range(3, 8):
        counts = {}
        for parents in iproduct(*[range(1, k + 1) for k in range(1, n)]):   # parent of k+1 in 1..k
            size = [1] * (n + 1)
            for child in range(n, 1, -1):
                size[parents[child - 2]] += size[child]
            for v in range(2, n + 1):
                counts[(v, size[v])] = counts.get((v, size[v]), 0) + 1
        tot = 1
        for k in range(1, n):
            tot *= k
        for v in range(2, n + 1):
            for d in range(1, n - v + 2):
                ok &= Fraction(counts.get((v, d), 0), tot) == Fraction(comb(n - d - 1, v - 2), comb(n - 1, v - 1))
    check('beta_v(d) = C(n-d-1, v-2)/C(n-1, v-1) against all recursive trees, n <= 7', ok, 'exact enumeration')
    # d/d eps f_n(m) at eps = 0 equals n/(m(m+1)) for 1 <= m <= n-1, so the first-order term is x/(m(m+1)).
    ok = True
    for n in range(2, 16):
        # the chain with eps as a formal variable, kept to first order: pairs (value, eps-coefficient)
        c0 = [Fraction(0)] * (n + 1)
        c1 = [Fraction(0)] * (n + 1)
        c0[0] = Fraction(1)
        for t in range(1, n):
            n0 = [Fraction(0)] * (n + 1)
            n1 = [Fraction(0)] * (n + 1)
            for b in range(t):
                a0, a1 = Fraction(b, t), 1 - Fraction(2 * b, t)
                n0[b] += c0[b] * (1 - a0)
                n0[b + 1] += c0[b] * a0
                n1[b] += c1[b] * (1 - a0) - c0[b] * a1
                n1[b + 1] += c1[b] * a0 + c0[b] * a1
            c0, c1 = n0, n1
        ok &= all(c1[m] == Fraction(n, m * (m + 1)) for m in range(1, n))
    check('first-order term of f_n(m) is x/(m(m+1)) for every 1 <= m <= n-1, n <= 15', ok, 'exact')

    # ------------------------------------------------ Corollary 3.6: hypothesis x_n >= 2(1 - eps_n)
    print('\nCorollary 3.6: the hypothesis x_n >= 2(1 - eps_n), computed for n < 1688 and proved for even n >= 1688', flush=True)
    # C_n/E_n increases in eps (Proposition 2.3), and x = 2(1 - eps) means eps = 2/(n+2).
    # So x_n >= 2(1 - eps_n) exactly when C_n <= E_n at eps = 2/(n+2): one evaluation per n.
    t0 = time.time()
    holdsA, holdsB, margin = [], [], 0.0
    for n in range(2, 1688):
        e0 = 2.0 / (n + 2)
        PA = law_A(n, e0)[0]
        PB = law_B(n, e0)
        if center_of(PA, n) <= PA[n]:
            holdsA.append(n)
        if center_of(PB, n) <= PB[n]:
            holdsB.append(n)
        if n >= 8:
            margin = max(margin, center_of(PA, n) / PA[n])
    check('hypothesis holds for every 8 <= n < 1688 (after Corollary 3.6) and fails for every n <= 7 (research notes, not printed)',
          holdsA == holdsB == list(range(8, 1688)),
          f'A and B agree; first n where it holds: {holdsA[0]}; largest C_n/E_n at eps = 2/(n+2) for n >= 8: {margin:.3f}'
          f'  [{time.time() - t0:.0f}s]')
    # The proof for even n >= 1688 (text after Corollary 3.6): at eps = 2/n, Theorem 2.6(b) applies and C_n < E_n.
    first = next(n for n in range(64, 4000, 2) if (2 / n) * (1 + log(n)) <= 0.01)
    check('eps(1 + log n) <= 1/100 at eps = 2/n holds for every even n >= 1688 and fails at n = 1686 (after Corollary 3.6)',
          first == 1688, f'first even n: {first}; the left side decreases in n')
    ns = np.arange(1688, 10 ** 6, 2, dtype=float)
    ub = 8 * ns ** (4 / ns) * np.exp(10400 / ns) / (ns * (ns + 2))
    check('8 n^(4/n) e^(10400/n)/(n(n+2)) decreases in n and is below 1.4e-3 at n = 1688 (after Corollary 3.6)',
          bool(np.all(np.diff(ub) < 0)) and ub[0] < 1.4e-3, f'{ub[0]:.4e} at n = 1688 (checked up to 10^6; each factor decreases)')
    En = 0.5 * (1 - 2 / ns) ** (ns - 1)
    lowE = 0.5 * np.exp(-2 - 2 / ns)
    check('E_n = (1/2)(1 - 2/n)^(n-1) >= (1/2) e^(-2-2/n) > 0.06 for even n >= 1688 (after Corollary 3.6)',
          bool(np.all(En >= lowE)) and lowE.min() > 0.06, f'smallest lower bound {lowE.min():.4f}')

    # ------------------------------------------------ crossings for every n <= 600 and the shape there
    print('\nShape at the crossing for 2 <= n <= 600 (Theorem 3.5, Corollary 3.6, Conjecture 3.10)', flush=True)
    t0 = time.time()
    XA, XB = {}, {}
    prev = None
    for n in range(2, 601):
        if prev is None:
            lo, hi = 0.05, 1.9
        else:
            lo, hi = max(0.05, prev - 0.2), min(prev + 0.4, 0.9 * n)
        xa = crossing(n, 'A', lo, hi)
        XA[n] = xa
        prev = xa
        step = 1 if args.full else 7
        if n % step == 0 or n <= 60:
            XB[n] = crossing(n, 'B', lo, hi)
    dx = max(abs(XA[n] - XB[n]) for n in XB)
    check('crossings for 2 <= n <= 600 by methods A and B', dx < 1e-9,
          f'{len(XB)} values of n compared, largest difference {dx:.1e}  [{time.time() - t0:.0f}s]')
    agree('x_2 = 2/3 (research notes, not printed)', '0.6666666667', {'A': XA[2]})
    agree('x_12 (research notes, not printed)', '2.035', {'A': XA[12]})
    dipfail, shapefail, openfail, closedfail, minfail = [], [], [], [], []
    for n in range(2, 601):
        PA = law_A(n, XA[n] / n)[0]
        if n in (2, 3):
            check(f'n = {n}: bin n-1 is a central bin, so P(A_n = n-1) = E_n at the crossing',
                  abs(PA[n - 1] / PA[n] - 1) < 1e-9, f'ratio {PA[n - 1] / PA[n]:.12f}')
            continue
        S = shape(PA, n)
        if not S['dip']:
            dipfail.append(n)
        if n >= 10:
            if S['changes'] != 3:
                shapefail.append(n)
            if S['open_bad']:
                openfail.append(n)
            if S['end_bad']:
                closedfail.append(n)
            if not S['unique_min']:
                minfail.append(n)
    check('dip P(A_n = n-1) > E_n at the crossing for every 4 <= n <= 600 (research notes, not printed)', not dipfail, f'failures {dipfail}')
    check('exactly 3 sign changes of the first difference, 10 <= n <= 600 (research notes, not printed)', not shapefail, f'failures {shapefail}')
    check('center bin(s) the unique interior minimum, 10 <= n <= 600 (research notes, not printed)', not minfail, f'failures {minfail}')
    check('Conjecture 3.10 (open range) holds for every 10 <= n <= 600 (after it)', not openfail, f'failures {openfail}')
    expect = [10, 11] + list(range(17, 23)) + list(range(30, 36)) + list(range(48, 52))
    check('closed-range version fails exactly at n = 10, 11, 17-22, 30-35, 48-51 (endpoints only; the paper says only for some n <= 51)',
          closedfail == expect, f'failures {closedfail}')

    # ------------------------------------------------ the doubling grid
    print('\nThe grid n = 50, ..., 25600 (Remark 3.7, Conjecture 3.10, Figure 2)', flush=True)
    grid = [50, 100, 200, 400, 800, 1600, 3200, 6400, 12800] + ([25600] if args.full else [])
    ms_paper = {1600: 21, 3200: 25, 6400: 29, 12800: 33, 25600: 38}
    a1_paper = {1600: 33, 3200: 39, 6400: 45, 12800: 51, 25600: 57}
    X = {}
    for n in grid:
        t1 = time.time()
        g = g_root(n)
        x = crossing_window(n, 0.5 * g, g + 0.5)
        X[n] = x
        PA, fA = law_A(n, x / n)
        SA = shape(PA, n)
        line = f'x = {x:.6f}, m* = {SA["ms"]}, a_1 = {SA["a1"]}, 2m* = {2 * SA["ms"]}'
        okB = True
        if n <= 12800 or args.full:
            PB = law_B(n, x / n)
            SB = shape(PB, n)
            okB = (SB['ms'], SB['a1'], SB['changes']) == (SA['ms'], SA['a1'], SA['changes'])
            okB &= float(np.max(np.abs(PB / PA - 1))) < 1e-9
        ok = SA['changes'] == 3 and SA['unique_min'] and SA['dip'] and not SA['open_bad'] and okB
        if n in ms_paper:
            cpm = int(np.argmax(cp_panjer(x, n, 400)))
            ok &= SA['ms'] == ms_paper[n] == cpm and SA['a1'] == a1_paper[n]
            line += f', CP_n mode {cpm} (m* equal to the CP_n mode is in Remark 3.7; notes: m* = {ms_paper[n]}, a_1 = {a1_paper[n]})'
        check(f'n = {n}: open-range convexity (Conjecture 3.10, printed for n = 800, ..., 25600), m* = CP_n mode (Remark 3.7); 3 sign changes, dip, unique central minimum (research notes, not printed)', ok,
              line + f', A and B agree: {okB}  [{time.time() - t1:.1f}s]')
        if n in (1600, 3200):
            ratioA = fA[1:n // 2 + 1] / cp_panjer(x, n, n // 2)[1:]
            fB = law_B(n, x / n, 'plus')[::-1]
            ratioB = fB[1:n // 2 + 1] / cp_fft(x, n, n // 2)[1:]
            agree(f'min f_n/CP_n over 1 <= m <= n/2 at n = {n} (research notes, not printed)', {1600: '0.931', 3200: '0.956'}[n],
                  {'A': float(ratioA.min()), 'B': float(ratioB.min())},
                  f'; attained at m = n/2: {int(np.argmin(ratioA)) + 1 == n // 2 == int(np.argmin(ratioB)) + 1}')
            check(f'the minimum of f_n/CP_n at n = {n} is attained at m = n/2 (research notes, not printed)',
                  int(np.argmin(ratioA)) + 1 == n // 2 == int(np.argmin(ratioB)) + 1,
                  f'argmin A {int(np.argmin(ratioA)) + 1}, B {int(np.argmin(ratioB)) + 1}')
        if n == 3200:
            eps = x / n
            R1 = PA[n - 1] / PA[n]
            lo1 = x / (2 * (1 - eps))
            hi1 = x * (1 + 1 / n) ** 2 / (2 - 3 * eps) + eps / (1 - eps)
            agree('Theorem 3.5 lower bound at n = 3200 (research notes, not printed)', '5.7943', {'formula': lo1})
            agree('Theorem 3.5 upper bound at n = 3200 (research notes, not printed)', '5.8121', {'formula': hi1})
            agree('P(A_n = n-1)/E_n at n = 3200 (research notes, not printed)', '5.8048', {'A': R1, 'B': PB[n - 1] / PB[n]})
            agree('max f_n/CP_n over 1 <= m <= n/2 at n = 3200 (research notes, not printed)', '1.0140',
                  {'A': float(ratioA.max()), 'B': float(ratioB.max())})
            check('Figure 2 check value m* = 25 at n = 3200', SA['ms'] == 25, f'm* = {SA["ms"]}')
        if n == 6400:
            # Heuristic H3: the law given the first step is concave for n - m between m_h + 1 and
            # about 0.68 (x n^2)^(1/3).
            sd = np.zeros(n + 1)
            sd[1:n] = fA[:-2] - 2 * fA[1:-1] + fA[2:]
            neg = [m for m in range(n // 2 + 1, n) if sd[m] < 0]
            mh = int(np.argmax(fA))
            r_lo, r_hi = n - neg[-1], n - neg[0]
            contiguous = neg == list(range(neg[0], neg[-1] + 1))
            agree('far-end concave stretch of f_n at n = 6400: r_hi/(x n^2)^(1/3)', '0.68',
                  {'A': r_hi / (x * n * n) ** (1 / 3)}, f'; r_lo = {r_lo} = m_h + 1: {r_lo == mh + 1}; '
                  f'one stretch: {contiguous}')
    if not args.full:
        print('  skip  n = 25600 (m* = 38, a_1 = 57); run with --full')

    # ------------------------------------------------ explicit bounds of the research notes (not printed)
    print('\nWhere the explicit bounds behind Appendix B say something (research notes, not printed)', flush=True)
    HH = np.concatenate([[0.0], np.cumsum(1.0 / np.arange(1, 2 * 10 ** 6 + 2))])
    H = lambda k: HH[k]

    def e_bound(m, n, x):
        """e_1(m) for m <= n/4 and e_2(m) for m > n/4 (explicit form of Proposition B.5 in the research notes)."""
        eps = x / n
        if m <= n / 4:
            return 2 * x / (m + 2) + x * H(m) / m + 2 * eps * H(m + 1) + 11 * eps * H(2 * m) + 4 * (m + 2) * exp(-(m - 1) / 9)
        r = n - m
        tau = (n / r) * (0.7 * r + 31) * exp(-(r - 8) / 40)
        return 2 * x / (m + 2) + x * H(m) / m + 8 * x * H(n) / r + 3 * x * H(n) / (m + 2) + tau

    def e_bound_B(m, n, x):
        """The same, written term by term from the statement with mpmath harmonic numbers."""
        eps = x / n
        Hm = float(mp.harmonic(m))
        if m <= n / 4:
            terms = [2 * x / (m + 2), x * Hm / m, 2 * eps * float(mp.harmonic(m + 1)),
                     11 * eps * float(mp.harmonic(2 * m)), 4 * (m + 2) * exp(-(m - 1) / 9)]
        else:
            r = n - m
            Hn = float(mp.harmonic(n))
            terms = [2 * x / (m + 2), x * Hm / m, 8 * x * Hn / r, 3 * x * Hn / (m + 2),
                     n * (0.7 + 31 / r) * exp(-(r - 8) / 40)]
        return sum(terms)

    for n, lo_p, hi_p in ((1600, 164, 400), (3200, 118, 2215)):
        x = X[n]
        fA = law_A(n, x / n)[1]
        ra = [m for m in range(2, n - 15) if e_bound(m, n, x) < 1]
        rb = [m for m in range(2, n - 15) if e_bound_B(m, n, x) < 1]
        viol = [m for m in range(2, n - 15) if fA[m] < x / (m * (m + 1)) * (1 - e_bound(m, n, x)) - 1e-18]
        contig = ra == list(range(ra[0], ra[-1] + 1))
        check(f'explicit Proposition B.5 is nontrivial at n = {n} exactly for {lo_p} <= m <= {hi_p} (research notes, not printed)',
              (ra[0], ra[-1]) == (rb[0], rb[-1]) == (lo_p, hi_p) and contig and not viol,
              f'A [{ra[0]}, {ra[-1]}], B [{rb[0]}, {rb[-1]}], one interval: {contig}; '
              f'violations of the bound by the exact law: {len(viol)}')

    def xcross(n):
        return g_root(n)

    def delta_c0(m, x, eps):
        return x / m * (36 * log(m) + 256 * H(m) * log(m / x) + 33) + (m / x) * exp(eps + 0.11 * x - 0.093 * m)

    # Explicit form of Proposition B.6 (cumulative upper bound, research notes) against the exact tail, where it applies (m >= 16 x log m).
    for n in (3200, 6400):
        x = X[n]
        eps = x / n
        fA = law_A(n, eps)[1]
        tail = np.cumsum(fA[::-1])[::-1]                   # tail[m] = P(M_n >= m)
        ms = [m for m in range(6, n // 2 + 1) if m >= 16 * x * log(m)]
        viol = [m for m in ms if tail[m] > x * (1 / m - 1 / n) + (x / m) * delta_c0(m, x, eps)]
        check(f'explicit Proposition B.6 holds at n = {n} where it applies (research notes, not printed)', not viol,
              f'm in [{ms[0]}, {ms[-1]}], delta_c there at least {delta_c0(ms[-1], x, eps):.1f}, violations {len(viol)}')
    first = next(m for m in range(1000, 10 ** 7, 1000) if delta_c0(m, 20.0, 0.0) < 1)
    check('delta_c only becomes small for m of order 1e6 when x = 20 (research notes, not printed)', 5e5 <= first <= 2e6,
          f'delta_c(m) < 1 from about m = {first}')

    def Hbig(k):
        return float(mp.harmonic(k)) if k > 2 * 10 ** 6 else H(k)

    def delta_c(m, x, eps):
        return x / m * (36 * log(m) + 256 * Hbig(m) * log(m / x) + 33) + (m / x) * exp(eps + 0.11 * x - 0.093 * m)

    def delta_ell(m, n, x):
        eps = x / n
        first = (2 * x / (m + 3) + x * Hbig(m + 1) / (m + 1) + 4 * (m + 3) * exp(-m / 9) + 13 * eps * Hbig(n)) if m < n / 4 else 0.0
        return first + (x * (17 + 33 * Hbig(n) + 65 * Hbig(n) ** 2) + 32 + 40.1 * log(11 * n)) / n

    def at_center(n):
        """Hypotheses of the explicit Proposition B.8 at m = n/2, Delta(n/2), and the two factors of the explicit center bound of the research notes (not printed)."""
        x = xcross(n)
        eps = x / n
        m = n // 2
        m2 = floor(2 * m / 3)
        l0 = ceil(8 * x * (3 + log(x))) + 100
        m1 = (l0 + 1) * (1 + 2 * Hbig(l0))
        hyp = (n >= 1000 and 13 * eps * (1 + Hbig(n)) <= 1 / 8 and l0 <= n / 4
               and m2 >= max(m1, 16 * x * log(m), E_CONST ** 2 * x))
        D = delta_c(m2, x, eps) + delta_ell(m, n, x)
        r = n - m
        tau = (n / r) * (0.7 * r + 31) * exp(-(r - 8) / 40)
        e2 = 2 * x / (m + 2) + x * Hbig(m) / m + 8 * x * Hbig(n) / r + 3 * x * Hbig(n) / (m + 2) + tau
        return hyp, D, 1 + 3 * D ** 0.5 + 6 / n, 1 - e2

    lo_, hi_ = 1e6, 1e12
    for _ in range(60):
        mid = (lo_ * hi_) ** 0.5
        hyp, D, up, _ = at_center(int(mid) // 2 * 2)
        if hyp and D <= 1 / 16:
            hi_ = mid
        else:
            lo_ = mid
    n_up = int(hi_) // 2 * 2 + 2
    hyp, D, up_thr, _ = at_center(n_up)
    agree('explicit center upper bound first applies at the crossing (n ~ 1.107e8, research notes, not printed)', '1.107e8', {'bisection': hi_})
    agree('upper factor there (about 1.75, research notes, not printed)', '1.75', {'formula': up_thr}, f'; Delta = {D:.5f}')
    hyp8, D8, up8, _ = at_center(10 ** 8)
    agree('upper factor at n = 1e8, where Delta > 1/16 (research notes, not printed)', '1.78', {'formula': up8},
          f'; Delta = {D8:.4f}, Delta <= 1/16: {D8 <= 1 / 16}')
    lo_, hi_ = 10, 1e8
    for _ in range(60):
        mid = (lo_ * hi_) ** 0.5
        if at_center(int(mid) // 2 * 2)[3] > 0:
            hi_ = mid
        else:
            lo_ = mid
    agree('lower factor 1 - e_2(n/2) at the center first positive (n ~ 2.2e3, research notes, not printed)', '2.2e3', {'bisection': hi_})

    check('x L^2 >= log^2 2 > 1/3, not > 1/2, in the explicit proof of Theorem 3.8 (research notes, not printed)',
          log(2) ** 2 > 1 / 3 and log(2) ** 2 < 1 / 2, f'log^2 2 = {log(2) ** 2:.4f}')

    # ------------------------------------------------ Remark 3.7 and Theorem 3.8 at large n
    print('\nCompound Poisson proxy, the mode and the tail at large n (Remark 3.7, Theorem 3.8)', flush=True)
    n, x = 10 ** 6, g_root(10 ** 6)
    Hn = float(mp.harmonic(n))
    dB = x * x * log(n) / n + 4 * x * x / n * exp(4 * x * x / n) + 4 * x * x * (Hn * Hn + Hn) / n
    agree('delta_B at n = 1e6 and x = g_n (about 0.46, Remark 3.7)', '0.46', {'formula': dB})
    agree('2x at n = 1e6 (research notes, not printed)', '44.9', {'formula': 2 * x})
    for n, mp_ in ((10 ** 5, 47), (10 ** 6, 64)):
        t1 = time.time()
        x = g_root(n)
        hA = chain_A(n, x / n, 0, 300)
        vals = [int(np.argmax(hA))]
        if n < 10 ** 6 or args.full:
            vals.append(int(np.argmax(chain_B(n, x / n, 0, 300))))
        vals.append(int(np.argmax(cp_panjer(x, n, 300))))
        vals.append(int(np.argmax(cp_fft(x, n, 300))))
        check(f'mode of f_n at n = {n}, x = {x:.4f}, equal to the mode of CP_n (research notes, not printed)', all(v == mp_ for v in vals),
              f'notes {mp_}; chain(s) and CP_n (Panjer, FFT): {vals}  [{time.time() - t1:.1f}s]')
    t1 = time.time()
    n, x, m = 10 ** 6, 22.4407, 10 ** 4
    h0 = chain_A(n, x / n, 0, m)
    h1 = chain_A(n, x / n, 1, m)
    RA = 0.5 * (h0[m] + h1[m]) / (x / m ** 2)
    cpa = cp_panjer(x, n, m)
    devA = float(np.max(np.abs(h0[1:] / cpa[1:] - 1)))
    vals, devs = {'A': RA}, {'A': devA}
    if args.full:
        g0 = chain_B(n, x / n, 0, m)
        g1 = chain_B(n, x / n, 1, m)
        vals['B'] = 0.5 * (g0[m] + g1[m]) / (x / m ** 2)
        devs['B'] = float(np.max(np.abs(g0[1:] / cp_fft(x, n, m)[1:] - 1)))
    agree('P(A_n = n-m)/(x/m^2) at n = 1e6, x = 22.4407, m = 1e4 (after Theorem 3.8)', '0.51889', vals, f'  [{time.time() - t1:.0f}s]')
    agree('max over m <= 1e4 of |f_n/CP_n - 1| at n = 1e6 (Remark 3.7)', '3.5e-4', devs)
    check('Figure 2 check value 0.51889', abs(RA - 0.51889) < 5e-6, f'{RA:.6f}')
    if not args.full:
        print('  skip  second method (pull recursion, FFT proxy) at n = 1e6; run with --full')
    # Heuristic H2 near m = 70 at n = 1600 (discussion after Theorem 3.8).
    x = X[1600]
    H2 = 1 + x * (2 * log(70) + 2 * GAMMA - 3) / 70
    check('heuristic correction 1 + x(2 log m + 2 gamma - 3)/m is still close to 2 at m = 70, n = 1600 (after Theorem 3.8)',
          1.9 < H2 < 2.1, f'{H2:.4f}')

    # ------------------------------------------------ Landau constants (Remark 3.7)
    print('\nLandau constants (Remark 3.7 and the research notes)', flush=True)
    mp.mp.dps = 30
    l0A = mp.findroot(lambda l: landau_real(l, 1), -0.22)
    l0B = mp.findroot(lambda l: landau_fourier(l, 1), -0.22)
    agree('mode lambda_0 of f_L (Remark 3.7 prints -0.2228)', '-0.2227829813', {'A': float(l0A), 'B': float(l0B)})
    f2A, f2B = landau_real(l0A, 2), landau_fourier(l0B, 2)
    agree("f_L''(lambda_0) (computed, not certified, Remark 3.7)", '-0.0789', {'A': float(f2A), 'B': float(f2B)})
    f3A, f3B = landau_real(l0A, 3), landau_fourier(l0B, 3)
    agree('kappa_1/2 = f_L\'\'\'/(2 f_L\'\') in H1 (research notes, not printed)', '-0.535021', {'A': float(f3A / f2A / 2), 'B': float(f3B / f2B / 2)})

    def Kp(lam):
        def g(t):
            if t == 0:
                return mp.mpf(0)
            return mp.re(1j * t ** 3 * (mp.log(t) - 1j * mp.pi / 2) * mp.exp(-1j * lam * t)
                         * mp.exp(-1j * t * mp.log(t) - mp.pi * t / 2))
        return mp.quad(g, mp.linspace(0, 80, 161)) / mp.pi
    k0 = f3B / f2B / 2 - Kp(l0B) / (2 * f2B)
    agree('kappa_0 in H1 (research notes, not printed)', '0.549151', {'B': float(k0)})

    def cp_inf_mode(x):
        """Mode of CP_infinity (jumps d >= 1 at rates x/(d(d+1))), interpolated by a parabola through
        the log of the law at the integer mode and its 2 neighbors. The Panjer recursion is linear, so
        it runs without normalization, rescaled when the values get large."""
        M = int(x * log(x) + 3 * x) + 50
        q = np.zeros(M + 1)
        q[0] = 1.0
        w = 1.0 / (np.arange(1, M + 1) + 1.0)
        for m in range(1, M + 1):
            q[m] = x / m * np.dot(q[m - 1::-1], w[:m])
            if q[m] > 1e250:
                q[:m + 1] *= 1e-250
        j = int(np.argmax(q))
        lq = np.log(q[j - 1:j + 2])
        return j + 0.5 * (lq[0] - lq[2]) / (lq[0] - 2 * lq[1] + lq[2])
    t1 = time.time()
    xs_h1 = [10 * 2 ** k for k in range(11 if args.full else 9)]
    diffs = [cp_inf_mode(xx) - (xx * log(xx) - 0.222783 * xx - 0.535021 * log(xx) + 0.549151) for xx in xs_h1]
    shrink = all(abs(diffs[i + 1]) < abs(diffs[i]) for i in range(len(diffs) - 1))
    check(f'H1 mode law against the interpolated mode of CP_infinity, x = 10, 20, ..., {xs_h1[-1]} (research notes, not printed): at most 0.28, '
          'largest at x = 10 and shrinking', max(abs(d) for d in diffs) <= 0.28 and shrink,
          'differences ' + ', '.join(f'{d:+.4f}' for d in diffs) + f'  [{time.time() - t1:.0f}s]')
    if not args.full:
        print('  skip  H1 at x = 5120 and 10240; run with --full')
    f0 = landau_real(l0A, 0)
    inner = min((f0 - landau_real(l0A + d, 0)) / d ** 2 for d in
                [mp.mpf(s) * k / 100 for k in range(1, 101) for s in (-1, 1)])
    kap = min(inner, f0 - landau_real(l0A - 1, 0), f0 - landau_real(l0A + 1, 0))
    kapB = min(landau_fourier(l0B, 0) - landau_fourier(l0B + 1, 0), landau_fourier(l0B, 0) - landau_fourier(l0B - 1, 0))
    agree('best kappa_L (numerical, research notes, not printed)', '0.0262', {'A': float(kap), 'B (value at |l - l_0| = 1)': float(kapB)})
    EL = lambda y: (mp.mpf('99.7') * mp.log(y) + 517) / y
    xs = mp.findroot(lambda y: EL(y) - kap / 2, 1e5)
    agree('E_L(x) < kappa_L/2 needs x above (about 1.3e5, research notes, not printed)', '1.3e5', {'A': float(xs)})
    agree('that is log n above about 6.5e4 at the crossing (research notes, not printed)', '6.5e4', {'A': float(xs / 2)})
    b = 1 / (2 * mp.pi)
    I1 = 2 * mp.quad(lambda t: t ** 2 * mp.exp(-b * t), [0, mp.inf])
    I2 = 2 * mp.quad(lambda t: t ** 2 * abs(mp.log(t)) * mp.exp(-b * t), [0, 1, mp.inf])
    agree('int t^2 e^(-|t|/(2 pi)) dt (research notes, not printed)', '992.2', {'quadrature': float(I1), 'closed form 4(2 pi)^3': float(4 * (2 * mp.pi) ** 3)})
    agree('int t^2 |log|t|| e^(-|t|/(2 pi)) dt (research notes, not printed)', '2739.5', {'quadrature': float(I2)})
    agree('coefficient 0.631 I_1/(2 pi) of (log x)/x in E_L (research notes, not printed)', '99.64', {'formula': float(mp.mpf('0.631') * I1 / (2 * mp.pi))})
    agree('coefficient (0.631 I_2 + 1.53 I_1)/(2 pi) of 1/x in E_L (research notes, not printed)', '516.7',
          {'formula': float((mp.mpf('0.631') * I2 + mp.mpf('1.53') * I1) / (2 * mp.pi))})
    check('1/2 + pi/24 <= 0.631 (research notes, not printed)', 0.5 + pi / 24 <= 0.631, f'{0.5 + pi / 24:.6f}')

    def ratio(th):
        s = mp.e ** (1j * th)
        psi = (1 - s) * mp.log(1 - s) / s
        R = psi + 1j * th * mp.log(-1j * th)
        return abs(R) / (th ** 2 * (mp.mpf('0.631') * abs(mp.log(th)) + mp.mpf('1.53')))
    grid_t = [mp.mpf(10) ** (-k / 4) for k in range(0, 49)] + [mp.pi * k / 400 for k in range(1, 401)]
    rmax = max(ratio(t) for t in grid_t)
    check('|R(theta)| <= theta^2 (0.631 |log theta| + 1.53) on a grid of (0, pi] (explicit form in the research notes, not printed)', rmax <= 1,
          f'largest ratio {float(rmax):.4f}')
    th = np.concatenate([np.logspace(-8, 0, 4000), np.linspace(1, np.pi, 4000)])
    reps = 2 * np.sin(th / 2) ** 2 * np.log(2 * np.sin(th / 2)) + np.sin(th) * (np.pi - th) / 2
    check('-Re Psi(theta) >= theta/(2 pi) on (0, pi] (research notes behind Remark 3.7)', float(np.min(reps / th)) >= 1 / (2 * pi),
          f'min ratio {float(np.min(reps / th)):.5f} against 1/(2 pi) = {1 / (2 * pi):.5f}')

    print(f'\nSection 3 checks done in {time.time() - T0:.0f}s: '
          + ('all passed.' if not FAILS else f'{len(FAILS)} FAILED: ' + '; '.join(FAILS)))
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
