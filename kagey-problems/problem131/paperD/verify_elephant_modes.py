"""Checks for Section 4.2 (the number of modes of the fixed-memory limit law).

 1. The constants in the proof of Theorem 4.3 (label thm:two-modes-near-one): the bounds
    M = exp((1-gamma) delta) and V = exp(2(1-gamma) delta)/(1-2 delta) - 1 at delta = 1/40, the
    Cantelli and Chebyshev bounds for F(2/5) and F(7/4), and the final comparison. Also, on a grid
    of a in [39/40, 1), the exact mean and variance of the limit L_a (from the moment recursion of
    Guerin, Laulin and Raschel, Theorem 1.4) against M and V.
 2. Step 1 of the proof of Theorem 4.2 (label thm:two-modes), as an illustration: the Gaussian
    smoothing V_N of the second differences of P_N has at most the pattern (+,-,+,-,+) on a grid.
 3. Remark 4.4 (label rem:modes-threshold), numerical and not a proof input: the value of a at
    which the second difference of the exact finite law at the center changes sign, for
    N = 1000, 4000 and 8000 (the paper quotes 0.6563 and 0.6592 for N = 4000 and 8000).
 4. Remark 4.4, numerical: the sign of g_a''(0) for the limit law on the grid a = 0.55..0.85,
    computed from the moments by the cosine series in ball arithmetic (python-flint), and the
    change of sign a_c = 0.66881.
The output is written to data/verify_modes_output.txt after a header line with the sha256 of this
script and the software versions. --quick and --full do the same (the script takes about a minute).
Run: python -B verify_elephant_modes.py
"""
import datetime
import hashlib
import math
import platform
import sys
import time
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import numpy as np
import flint
from flint import arb, ctx

HERE = Path(__file__).resolve().parent
OUT = HERE / 'data' / 'verify_modes_output.txt'
LINES = []
FAILS = []


def emit(s=''):
    print(s, flush=True)
    LINES.append(s)


def check(label, ok, detail=''):
    emit(('  ok    ' if ok else '  FAIL  ') + label + (': ' + detail if detail else ''))
    if not ok:
        FAILS.append(label)


# ---------------------------------------------------------------- part 1
def part1():
    emit('1. Constants in the proof of Theorem 4.3 (a >= 39/40)')
    mp.mp.dps = 50
    g = mp.euler
    d = mp.mpf(1) / 40
    M = mp.e ** ((1 - g) * d)
    V = mp.e ** (2 * (1 - g) * d) / (1 - 2 * d) - 1
    check('M = exp((1-gamma)/40) <= 1.0107', M <= mp.mpf('1.0107'), mp.nstr(M, 10))
    check('V = exp(2(1-gamma)/40)/(1-2/40) - 1 <= 0.0752', V <= mp.mpf('0.0752'), mp.nstr(V, 10))
    Vb, Mb = mp.mpf('0.0752'), mp.mpf('1.0107')
    Fs = Vb / (Vb + mp.mpf(9) / 25)
    Fr = 1 - Vb / (mp.mpf(7) / 4 - Mb) ** 2
    check('F(2/5) <= V/(V+9/25) <= 0.173', Fs <= mp.mpf('0.173'), mp.nstr(Fs, 10))
    check('F(7/4) >= 1 - V/(7/4-M)^2 >= 0.862', Fr >= mp.mpf('0.862'), mp.nstr(Fr, 10))
    lhs, rhs = mp.mpf('2.5') * mp.mpf('0.173'), mp.mpf(4) / 7 * mp.mpf('0.862')
    check('(5/2) 0.173 <= 0.433 < 0.492 <= (4/7) 0.862', lhs <= mp.mpf('0.433') and rhs >= mp.mpf('0.492'),
          f'{mp.nstr(lhs, 6)} and {mp.nstr(rhs, 6)}')
    # exact moments on a grid of a against the bounds
    worst_mu, worst_v = mp.mpf(0), mp.mpf(0)
    ok_mu, ok_v, ok_rec = True, True, True
    for i in range(0, 1000):
        a = mp.mpf(39) / 40 + mp.mpf(i) / 40000
        delta = 1 - a
        mu = 1 / mp.gamma(1 + a)
        m2 = 1 / ((2 * a - 1) * mp.gamma(2 * a))
        # the recursion of Theorem 1.4: m_1 = 1, m_2 = a/(2a-1), E L^k = (k-1)! m_k / (a Gamma(k a))
        rec1 = 1 / (a * mp.gamma(a))
        rec2 = (a / (2 * a - 1)) / (a * mp.gamma(2 * a))
        ok_rec &= abs(rec1 - mu) < mp.mpf(10) ** -40 and abs(rec2 - m2) < mp.mpf(10) ** -40
        v = m2 - mu ** 2
        Ma = mp.e ** ((1 - g) * delta)
        Va = mp.e ** (2 * (1 - g) * delta) / (1 - 2 * delta) - 1
        ok_mu &= (1 <= mu <= Ma)
        ok_v &= (v <= Va)
        worst_mu = max(worst_mu, mu)
        worst_v = max(worst_v, v)
    check('moment recursion (k = 1, 2) gives 1/Gamma(1+a) and 1/((2a-1)Gamma(2a))', ok_rec,
          '1000 values of a in [39/40, 1)')
    check('1 <= E L_a <= exp((1-gamma)(1-a)) on the grid', ok_mu, f'largest E L_a {mp.nstr(worst_mu, 8)}')
    check('Var L_a <= V(1-a) on the grid', ok_v, f'largest Var L_a {mp.nstr(worst_v, 8)} (paper bound 0.0752)')
    emit()


# ---------------------------------------------------------------- finite law
def law(N, eps):
    """P(A_N = k), k = 0..N, fair first step, double precision."""
    c = 1 - 2 * eps
    P = np.zeros(N + 2)
    P[0] = P[1] = 0.5
    k = np.arange(N + 2)
    for t in range(1, N):
        r = eps + c * k / t
        Q = P * (1 - r)
        Q[1:] += (P * r)[:-1]
        P = Q
    return P[:N + 1]


def law_exact(N, eps):
    c = 1 - 2 * eps
    P = [Fraction(1, 2), Fraction(1, 2)]
    for t in range(1, N):
        Q = [Fraction(0)] * (t + 2)
        for k in range(t + 1):
            r = eps + c * Fraction(k, t)
            Q[k] += P[k] * (1 - r)
            Q[k + 1] += P[k] * r
        P = Q
    return P


def sign_pattern(z, tol=0.0):
    out = []
    for v in z:
        s = 1 if v > tol else (-1 if v < -tol else 0)
        if s and (not out or out[-1] != s):
            out.append(s)
    return out


def is_subseq(p, q):
    it = iter(q)
    return all(any(x == y for y in it) for x in p)


PI5 = [1, -1, 1, -1, 1]


def part2():
    emit('2. Step 1 of the proof of Theorem 4.2 (illustration)')
    worst = 0.0
    for N in (12, 40):
        for eps in (Fraction(1, 9), Fraction(1, 5)):
            P = law_exact(N, eps)
            Pd = law(N, float(eps))
            worst = max(worst, max(abs(float(x) - y) / float(x) for x, y in zip(P, Pd)))
    check('double-precision law against exact rationals, N = 12, 40', worst < 1e-12, f'largest relative error {worst:.1e}')
    N = 2000
    for a in (0.6, 0.7, 0.8, 0.9):
        eps = (1 - a) / 2
        P = law(N, eps)
        D = P[2:] - 2 * P[1:-1] + P[:-2]            # D_N(1..N-1)
        z = (2 * np.arange(1, N) - N) / N ** a
        pD = sign_pattern(D, 1e-300)
        for sigma in (0.05, 0.2):
            y = np.linspace(-3, 3, 1201)
            # V_N up to the positive factor eta^-2; evaluate as an exponential sum in log space
            V = np.array([np.sum(D * np.exp(-(yy - z) ** 2 / (2 * sigma ** 2))) for yy in y])
            scale = np.max(np.abs(V))
            pV = sign_pattern(V, 1e-9 * scale)
            check(f'a = {a}, sigma = {sigma}: sp(D_N) <= Pi5 and sp(V_N on a grid) <= Pi5',
                  is_subseq(pD, PI5) and is_subseq(pV, PI5), f'sp(V_N) = {pV}')
    emit()


def center_curv(N, a):
    P = law(N, (1 - a) / 2)
    h = N // 2
    return (P[h + 1] - 2 * P[h] + P[h - 1]) / P[h]


def part3():
    emit('3. Remark 4.4: the finite-N center threshold (numerical)')
    vals = {}
    for N in (1000, 4000, 8000):
        t0 = time.time()
        lo, hi = 0.6, 0.7
        ok = center_curv(N, lo) < 0 < center_curv(N, hi)
        while hi - lo > 1e-7:
            mid = (lo + hi) / 2
            if center_curv(N, mid) < 0:
                lo = mid
            else:
                hi = mid
        vals[N] = (lo + hi) / 2
        check(f'N = {N}: D_N(N/2) < 0 at a = 0.6 and > 0 at a = 0.7, sign change bracketed', ok,
              f'a = {vals[N]:.6f}  [{time.time() - t0:.1f}s]')
    check('N = 4000 rounds to 0.6563 (Remark 4.4)', round(vals[4000], 4) == 0.6563, f'{vals[4000]:.6f}')
    check('N = 8000 rounds to 0.6592 (Remark 4.4)', round(vals[8000], 4) == 0.6592, f'{vals[8000]:.6f}')
    check('the values increase with N', vals[1000] < vals[4000] < vals[8000])
    emit()


# ---------------------------------------------------------------- limit law
def dyadic(aflt):
    return arb(round(aflt * 2 ** 50)) / 2 ** 50


def cos_coeffs(a, K):
    """Coefficients of t^(2k) in E cos(t L_a) = sum_k (-1)^k E L_a^(2k) t^(2k)/(2k)!, k <= K/2.
    E L_a^n = (n-1)! m_n / (a Gamma(n a)) with the recursion of GLR, Theorem 1.4."""
    m = [arb(0)] * (K + 1)
    m[1] = arb(1)
    cs = [arb(1) if j % 2 == 0 else a for j in range(K + 1)]
    for k in range(2, K + 1):
        s = arb(0)
        for j in range(1, k):
            s += cs[j] * m[j] * m[k - j]
        m[k] = s / (k * a - cs[k])
    out = [arb(1)]
    for k in range(1, K // 2 + 1):
        n = 2 * k
        out.append((-1) ** k * m[n] / (n * a * (n * a).gamma()))
    return out


def curvature_integral(aflt, K, T, prec):
    """I(a) = int_0^T t^2 E cos(t L_a) dt, so that g_a''(0) is about -I(a)/pi, and the value of the
    cosine series at t = T."""
    ctx.prec = prec
    cf = cos_coeffs(dyadic(aflt), K)
    Tb = arb(T)
    I, ph = arb(0), arb(0)
    for k, c in enumerate(cf):
        I += c * Tb ** (2 * k + 3) / (2 * k + 3)
        ph += c * Tb ** (2 * k)
    return I, ph


def params(a):
    if a <= 0.615:
        return 1500, 8, 1500
    if a <= 0.795:
        return 1200, 16, 1200
    return 3000, 34, 3000


def part4():
    emit('4. Remark 4.4: the sign of g_a\'\'(0) for the limit law (numerical)')
    signs = {}
    t0 = time.time()
    ok_all = True
    for i in range(55, 86):
        a = i / 100
        K, T, prec = params(a)
        I, ph = curvature_integral(a, K, T, prec)
        tail = float(abs(ph)) * T ** 2
        good = (not I.contains(0)) and tail < 1e-3 * float(abs(I))
        ok_all &= good
        signs[i] = 1 if I > 0 else -1
        emit(f'        a = {a:.2f}: int_0^{T} t^2 E cos(t L_a) dt = {I.str(6, radius=False)}, '
             f'T^2 |E cos(T L_a)| = {tail:.1e}')
    check('each value is enclosed away from 0 and the cut at T is below 1e-3 of it', ok_all,
          f'[{time.time() - t0:.0f}s]')
    neg = [i / 100 for i in signs if signs[i] < 0]
    pos = [i / 100 for i in signs if signs[i] > 0]
    check('g_a\'\'(0) < 0 exactly for a <= 0.66 on the grid', max(pos) == 0.66 and min(neg) == 0.67,
          f'g\'\'(0) < 0 for a in [{min(pos)}, {max(pos)}], > 0 for a in [{min(neg)}, {max(neg)}]')
    lo, hi = 0.66, 0.67
    while hi - lo > 1e-7:
        mid = (lo + hi) / 2
        I, _ = curvature_integral(mid, 900, 14, 900)
        if I > 0:
            lo = mid
        else:
            hi = mid
    ac = (lo + hi) / 2
    check('bisection: a_c = 0.66881 (Remark 4.4)', abs(ac - 0.66881) < 5e-6, f'a_c = {ac:.7f}')
    emit()


def main():
    src = Path(__file__).read_bytes()
    header = (f'# verify_elephant_modes.py sha256={hashlib.sha256(src).hexdigest()} '
              f'python={platform.python_version()} numpy={np.__version__} mpmath={mp.__version__} '
              f'python-flint={flint.__version__} date={datetime.date.today().isoformat()}')
    LINES.append(header)
    emit('Paper D, Section 4.2: the number of modes of the fixed-memory limit law')
    emit()
    t0 = time.time()
    part1()
    part2()
    part3()
    part4()
    if FAILS:
        emit(f'{len(FAILS)} checks failed: {FAILS}  ({time.time() - t0:.0f}s)')
    else:
        emit(f'All checks passed ({time.time() - t0:.0f}s).')
    OUT.write_text('\n'.join(LINES) + '\n', encoding='utf-8', newline='\n')
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
