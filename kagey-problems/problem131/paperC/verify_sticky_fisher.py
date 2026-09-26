"""Checks for Sections 7 and 8 and Appendices D and E of Paper C.

Part 1, sticky priors. The chain has transition matrix (1-h)I + h Pi with
h = tau log N / N, and Pi is a switching kernel (stochastic, zero diagonal).
Method A is a dynamic program for the exact law of the composition. Method B
uses other exact formulas: Paper A's polynomial S_{a,b} for a symmetric pair
(Corollary 7.5), the run expansion of Lemma 2.3 for the maximum on a face,
and powers of the killed matrices for the face masses (Proposition 7.6).
The probability of the direct jump under the sticky HDP prior is found by Monte
Carlo (10^6 draws, as in the paper) and by 2 quadratures in different
coordinates.

Part 2, the endpoint of Paper A's walk. Method A is the run formula of Paper A
(its run count), which gives the joint law of the endpoint and the number of
switches, and hence e_N(q) through Proposition 8.1. Method B is Paper A's
recurrence run with complex q, which gives the derivative in q exactly (the
complex-step method), and then e_N(q) from the definition of the Fisher
information. The moments of Lemma E.1 are checked in exact arithmetic, with q
as a symbol, for N = 1..12, which is the finite computation the proof uses.
The telegraph limit is an integral with Bessel functions (method A), compared
with the discrete efficiency at large N (method B).

Run with python -B verify_sticky_fisher.py, or add --full for the sticky
switches at N = 480 and the discrete telegraph comparison at N = 16000.
"""
import argparse
import itertools
import math
import sys
import time
from fractions import Fraction
from math import log, pi, sqrt

import mpmath as mp
import numpy as np
import sympy as sp
from scipy.integrate import quad
from scipy.optimize import brentq, minimize
from scipy.special import betainc, betaincinv, betaln, gammaln

from verify_second_order import RunFace, S_ab

FAILS = []


def check(label, ok, detail):
    print(('  ok    ' if ok else '  FAIL  ') + label + ': ' + detail, flush=True)
    if not ok:
        FAILS.append(label)


def tol_of(printed):
    s = printed.lstrip('+-')
    mant = s.split('e')[0]
    exp10 = int(s.split('e')[1]) if 'e' in s else 0
    dec = len(mant.split('.')[1]) if '.' in mant else 0
    return 0.5 * 10.0 ** (exp10 - dec) * (1 + 1e-9) + 1e-300


def agree(label, printed, values, extra=''):
    target = float(printed)
    t = tol_of(printed)
    ok = all(abs(float(v) - target) <= t for v in values.values())
    shown = ', '.join(f'{k} {float(v):.10g}' for k, v in values.items())
    check(label, ok, f'paper {printed}; {shown}{extra}')


# ---------------------------------------------------------------- Paper A's crossing

def logS(a, b, u):
    """log S_{a,b}(u) in log space (float)."""
    m1 = np.arange(1, a + 1)
    lu = log(u)
    lC = lambda n, r: gammaln(n + 1) - gammaln(r + 1) - gammaln(n - r + 1)
    terms = []
    for dm, c in ((-1, 1.0), (0, 2.0), (1, 1.0)):
        m2 = m1 + dm
        ok = (m2 >= 1) & (m2 <= b)
        t = log(c) + lC(a - 1, m1[ok] - 1) + lC(b - 1, m2[ok] - 1) + (m1[ok] + m2[ok] - 1) * lu
        terms.append(t)
    t = np.concatenate(terms)
    mx = t.max()
    return mx + log(np.exp(t - mx).sum())


def uN_runs(N):
    """Paper A's root: S_{N/2,N/2}(u) = 1 (method A, run formula)."""
    return brentq(lambda u: logS(N // 2, N - N // 2, u), 1e-9, 1.0, xtol=1e-16, rtol=1e-15)


def paperA_law(N, q):
    """P(K = k), k = 0..N, by Paper A's recurrence (works for complex q)."""
    p = 1 - q
    R = np.zeros(N + 1, dtype=complex)
    Lf = np.zeros(N + 1, dtype=complex)
    R[1] = 0.5
    Lf[0] = 0.5
    for n in range(2, N + 1):
        R2 = np.zeros(N + 1, dtype=complex)
        R2[1:] = p * R[:-1] + q * Lf[:-1]
        L2 = p * Lf + q * R
        R, Lf = R2, L2
    return R + Lf


def uN_dp(N):
    """Paper A's root from the recurrence: P_N(N/2) = P_N(0) (method B)."""
    f = lambda q: (lambda P: log(P[N // 2].real) - log(P[0].real))(paperA_law(N, q))
    q = brentq(f, 1e-6, min(0.5, 20 * log(N) / N), xtol=1e-15, rtol=1e-14)
    return q / (1 - q)


# ---------------------------------------------------------------- Part 1: sticky chain

def comp_law3(N, P, mu):
    """Exact law of (n_1, n_2) for a 3-state chain (n_3 = N - n_1 - n_2), by a dynamic program."""
    A = np.zeros((3, N + 1, N + 1))
    A[0, 1, 0] = mu[0]
    A[1, 0, 1] = mu[1]
    A[2, 0, 0] = mu[2]
    for _ in range(1, N):
        B = np.zeros_like(A)
        for s2 in range(3):
            src = P[0, s2] * A[0] + P[1, s2] * A[1] + P[2, s2] * A[2]
            if s2 == 0:
                B[0, 1:, :] += src[:-1, :]
            elif s2 == 1:
                B[1, :, 1:] += src[:, :-1]
            else:
                B[2] += src
        A = B
    return A.sum(0)


def map_support(D, N, tol=1e-10):
    m = D.max()
    locs = np.argwhere(D >= m * (1 - tol))
    sups = set()
    comps = []
    for a, b in locs:
        n = (int(a), int(b), N - int(a) - int(b))
        if n[2] < 0:
            continue
        sups.add(tuple(i for i in range(3) if n[i] > 0))
        comps.append(n)
    return sups, comps, m


def sticky_P(K, c, N):
    h = c * log(N) / N
    return (1 - h) * np.eye(len(K)) + h * K


def perron_root(M):
    return max(np.linalg.eigvals(M).real) if M.shape[0] > 1 else M[0, 0]


def thresholds(K):
    d = len(K)
    rho = {F: perron_root(K[np.ix_(F, F)]) for s in range(1, d + 1) for F in itertools.combinations(range(d), s)}
    cm = min((len(F) - 1) / rho[F] for F in rho if len(F) >= 2)
    cp = max((d - len(F)) / (1 - rho[F]) for F in rho if len(F) < d)
    return cm, cp, rho


K1 = np.array([[0, .9, .1], [.9, 0, .1], [.5, .5, 0]])


def check_kernels():
    print('\nProposition 7.2 and Corollary 7.3: thresholds and the direct jump', flush=True)
    cm, cp, rho = thresholds(K1)
    agree('Pi: rho_{1,2}', '0.9', {'numpy': rho[(0, 1)], 'closed': 0.9})
    agree('Pi: rho_{1,3} = sqrt(0.05)', '0.2236', {'numpy': rho[(0, 2)], 'closed': sqrt(0.05)})
    agree('Pi: tau_- = 10/9', '1.111', {'numpy': cm, 'closed': 10 / 9})
    agree('Pi: tau_+ = 10', '10', {'numpy': cp})
    rng = np.random.default_rng(3)
    bad = 0
    for trial in range(400):
        d = int(rng.integers(3, 6))
        K = rng.uniform(0.05, 1, (d, d))
        np.fill_diagonal(K, 0)
        K /= K.sum(1, keepdims=True)
        cm, cp, rho = thresholds(K)
        direct = all(rho[F] <= (len(F) - 1) / (d - 1) + 1e-12 for F in rho)
        bad += not (1 < cm <= d - 1 + 1e-12 and d - 1 - 1e-12 <= cp)
        bad += not ((abs(cm - (d - 1)) < 1e-9) == direct == (abs(cp - (d - 1)) < 1e-9))
        if d == 3:
            pairs = all(K[i, j] * K[j, i] <= 0.25 + 1e-12 for i, j in [(0, 1), (0, 2), (1, 2)])
            bad += pairs != direct
    for d in (3, 4, 5):
        U = (np.ones((d, d)) - np.eye(d)) / (d - 1)
        cm, cp, _ = thresholds(U)
        bad += not (abs(cm - (d - 1)) < 1e-9 and abs(cp - (d - 1)) < 1e-9)
    for a in (0.1, 0.5, 0.9):
        C = np.array([[0, a, 1 - a], [1 - a, 0, a], [a, 1 - a, 0]])
        cm, cp, _ = thresholds(C)
        bad += not (abs(cm - 2) < 1e-9 and abs(cp - 2) < 1e-9)
    # symmetric kernels: direct iff uniform (random symmetric doubly stochastic, zero diagonal)
    for trial in range(200):
        d = int(rng.integers(4, 7))
        S = rng.uniform(0.2, 1, (d, d))
        S = S + S.T
        np.fill_diagonal(S, 0)
        for _ in range(500):
            S /= S.sum(1, keepdims=True)
            S = (S + S.T) / 2
        cm, cp, _ = thresholds(S)
        bad += abs(cm - (d - 1)) < 1e-9
    check('(c), (d): 1 < tau_- <= d-1 <= tau_+, the direct-jump criterion, the d = 3 pair form, uniform and cyclic kernels, '
          'and no direct jump for random symmetric kernels', bad == 0, f'{bad} exceptions in 600 random kernels and the special ones')


def check_sticky_switches(full):
    print('\nCorollary 7.5 and the switches of the MAP for Pi', flush=True)
    # the dynamic program against a list of all 3^N paths, for a random kernel and start
    rng = np.random.default_rng(1)
    K = rng.random((3, 3))
    np.fill_diagonal(K, 0)
    K /= K.sum(1, keepdims=True)
    nu = rng.random(3)
    nu /= nu.sum()
    N = 8
    P = sticky_P(K, 1.3, N)
    D = comp_law3(N, P, nu)
    E = np.zeros_like(D)
    for w in itertools.product(range(3), repeat=N):
        pr = nu[w[0]]
        for a, b in zip(w, w[1:]):
            pr *= P[a, b]
        E[w.count(0), w.count(1)] += pr
    check('sticky dynamic program = all 3^N paths (paper: 1e-17)', np.abs(D - E).max() < 1e-16, f'max absolute difference {np.abs(D - E).max():.1e} at N = 8')
    # exact pair identity with rational numbers
    bad = total = 0
    Kf = [[Fraction(0), Fraction(9, 10), Fraction(1, 10)], [Fraction(9, 10), Fraction(0), Fraction(1, 10)], [Fraction(1, 2), Fraction(1, 2), Fraction(0)]]
    for h in (Fraction(1, 9), Fraction(2, 7)):
        P = [[(1 - h) if i == j else h * Kf[i][j] for j in range(3)] for i in range(3)]
        cur = {((1, 0, 0), 0): Fraction(1, 3), ((0, 1, 0), 1): Fraction(1, 3), ((0, 0, 1), 2): Fraction(1, 3)}
        for N in range(2, 11):
            nxt = {}                              # one more visit: cur now holds paths of length N
            for (c, i), p in cur.items():
                for j in range(3):
                    cc = list(c)
                    cc[j] += 1
                    nxt[(tuple(cc), j)] = nxt.get((tuple(cc), j), 0) + p * P[i][j]
            cur = nxt
            law = {}
            for (c, i), p in cur.items():
                law[c] = law.get(c, 0) + p
            for m in range(1, N):
                total += 1
                bad += law[(m, N - m, 0)] / law[(N, 0, 0)] != S_ab(m, N - m, h * Fraction(9, 10) / (1 - h))
    check("P_N(m e_1 + (N-m) e_2)/P_N(N e_1) = S_{m,N-m}(u), u = h pi_0/(1-h)", bad == 0, f'{total} exact cases, {bad} mismatches')
    mu = np.ones(3) / 3
    pair = RunFace([[0, .9], [.9, 0]], [1, 1], [1 / 3, 1 / 3], mmax=400)
    fullf = RunFace(K1, [1, 1, 1], mu, mmax=150)

    def logM(N, c):
        h = c * log(N) / N
        v = log(1 / 3) + (N - 1) * math.log1p(-h)
        e = pair.logP([N / 2, N / 2], h) if N % 2 == 0 else None
        f = lambda x: -fullf.logP([x[0] * N, x[0] * N, (1 - 2 * x[0]) * N], h) if 0 < x[0] < 0.5 else 1e300
        r = minimize(f, [0.4], method='Nelder-Mead', options=dict(xatol=1e-10, fatol=1e-14))
        a0 = int(round(r.x[0] * N))
        best = max(fullf.logP([a0 + i, a0 + j, N - 2 * a0 - i - j], h) for i in range(-3, 4) for j in range(-3, 4))
        return v, e, best
    printed = {60: ('0.8248', '4.804'), 120: ('0.8477', '5.340'), 240: ('0.8673', '5.779'), 480: ('0.8838', '6.139')}
    for N in ((60, 120, 240, 480) if full else (60, 120, 240)):
        uN = uN_runs(N)
        cpair = N * uN / ((0.9 + uN) * log(N))
        cB = brentq(lambda c: (lambda v: v[1] - v[0])(logM(N, c)), 0.5, 1.0, xtol=1e-10)
        c2 = brentq(lambda c: (lambda v: v[2] - v[1])(logM(N, c)), 3.0, 8.0, xtol=1e-8)
        # method A: the exact dynamic program changes its MAP support at both switches
        sides = []
        for c in (cpair - 2e-5, cpair + 2e-5, c2 - 2e-4, c2 + 2e-4):
            sups, comps, _ = map_support(comp_law3(N, sticky_P(K1, c, N), mu), N)
            sides.append(sorted(sups))
        okA = sides[0] == [(0,), (1,), (2,)] and sides[1] == [(0, 1)] and sides[2] == [(0, 1)] and sides[3] == [(0, 1, 2)]
        check(f'N = {N}: dynamic program: vertices (3-way tie) -> {{1,2}} -> [3] at these tau', okA, f'MAP supports {sides}')
        agree(f'N = {N}: first switch', printed[N][0], {'tau_pair': cpair, 'face maxima': cB})
        agree(f'N = {N}: second switch', printed[N][1], {'face maxima': c2})
    c0 = 0.5 * log(pi / 8)
    vals = []
    for N in (10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6):
        L = log(N)
        uN = uN_runs(N)
        cp = N * uN / ((0.9 + uN) * L)
        vals.append((cp * 0.9 - (1 - (0.5 * log(L) - c0) / L)) * L * L / log(L))
    check('tau_pair(N) = (1/pi_0)[1 - ((1/2)log L - c_0)/L + O(log L/L^2)]', max(abs(v) for v in vals) < 5,
          f'(remainder) L^2/log L = {np.round(vals, 3)} at N = 10^3..10^6')


def check_sticky_masses():
    print('\nTable 2 and Proposition 7.6: MAP against mass at N = 240', flush=True)
    N = 240
    mu = np.ones(3) / 3
    rows = {0.5: ('one', '0.0643', '0.465', '0.092', '0.379'), 0.8: ('one', '0.0122', '0.423', '0.034', '0.531'),
            3.0: ((120, 120, 0), '4.3e-8', '0.129', '3.3e-6', '0.871'), 8.0: ((111, 111, 18), '1.2e-21', '0.0081', '2.1e-16', '0.992')}
    pair = RunFace([[0, .9], [.9, 0]], [1, 1], [1 / 3, 1 / 3], mmax=240)
    fullf = RunFace(K1, [1, 1, 1], mu, mmax=150)
    for c, (mp_, p1, p12, poth, pall) in rows.items():
        h = c * log(N) / N
        P = sticky_P(K1, c, N)
        D = comp_law3(N, P, mu)
        n1, n2 = np.indices(D.shape)
        n3 = N - n1 - n2
        ok = n3 >= 0
        a, b, cc = n1 > 0, n2 > 0, n3 > 0
        mA = {'one': D[ok & ((a.astype(int) + b + cc) == 1)].sum(), '12': D[ok & a & b & ~cc].sum(),
              'oth': D[ok & ((a & ~b & cc) | (~a & b & cc))].sum(), 'all': D[ok & a & b & cc].sum()}
        # method B: masses from powers of the killed matrices and inclusion-exclusion
        sub = lambda F: float(mu[list(F)] @ np.linalg.matrix_power(P[np.ix_(F, F)], N - 1) @ np.ones(len(F)))
        one = sum(sub((i,)) for i in range(3))
        exact = lambda F: sub(F) - sum(sub((i,)) for i in F)
        mB = {'one': one, '12': exact((0, 1)), 'oth': exact((0, 2)) + exact((1, 2)), 'all': 1 - one - exact((0, 1)) - exact((0, 2)) - exact((1, 2))}
        sups, comps, _ = map_support(D, N)
        # method B for the MAP: the best composition of each face
        v = log(1 / 3) + (N - 1) * math.log1p(-h)
        e = max((pair.logP([k, N - k], h), (k, N - k, 0)) for k in range(1, N))
        f = max((fullf.logP([i, j, N - i - j], h), (i, j, N - i - j)) for i in range(60, 125) for j in range(60, 125) if N - i - j >= 1)
        best = max([(v, 'one'), e, f])[1]
        if mp_ == 'one':
            okmap = sorted(sups) == [(0,), (1,), (2,)] and best == 'one'
        else:
            okmap = comps[0] == mp_ and best == mp_ and len(comps) <= 2
        check(f'tau = {c}: MAP composition', okmap, f'dynamic program {comps[:3]}, face maxima {best}')
        agree(f'tau = {c}: P(one state)', p1, {'DP': mA['one'], 'powers': mB['one'], '(1-h)^(N-1)': (1 - h) ** (N - 1)})
        agree(f'tau = {c}: P(supp = {{1,2}})', p12, {'DP': mA['12'], 'powers': mB['12']})
        agree(f'tau = {c}: P(other pairs)', poth, {'DP': mA['oth'], 'powers': mB['oth']})
        agree(f'tau = {c}: P(supp = [3])', pall, {'DP': mA['all'], 'powers': mB['all']})
    # Proposition 7.6: the sandwich for every face with at least 2 states
    bad = 0
    for c in (0.5, 0.8, 3.0, 8.0):
        h = c * log(N) / N
        P = sticky_P(K1, c, N)
        for F in [(0, 1), (0, 2), (1, 2), (0, 1, 2)]:
            w, V = np.linalg.eig(K1[np.ix_(F, F)])
            i = int(np.argmax(w.real))
            r = np.abs(V[:, i].real)
            Lam = 1 - h * (1 - w[i].real)
            m = mu[list(F)].sum() * Lam ** (N - 1)
            val = float(mu[list(F)] @ np.linalg.matrix_power(P[np.ix_(F, F)], N - 1) @ np.ones(len(F)))
            bad += not (r.min() / r.max() * m * (1 - 1e-12) <= val <= r.max() / r.min() * m * (1 + 1e-12))
    check('Proposition 7.6: min r/max r <= P(supp in F)/(mu(F) Lambda_F^(N-1)) <= max r/min r', bad == 0, f'{bad} violations, 16 cases')


def hdp_route1(alpha):
    """P(direct) by quadrature in the Beta coordinates (B_3 innermost through the incomplete beta)."""
    a = alpha / 3.0
    lb = betaln(a, a)
    s = 1 / (2 * np.sqrt(2 * a + 1))
    W = min(0.5, 16 * s)
    f = lambda b: np.exp((a - 1) * (np.log(b) + np.log1p(-b)) - lb)
    F = lambda b: betainc(a, a, b)

    def inner(b1):
        U = min(1.0, 1 / (4 * (1 - b1)))
        hi2 = min(1.0, 1 / (4 * b1))
        lo2 = 0.0 if U >= 1 else max(0.0, 1 - 1 / (4 * (1 - U)))
        if hi2 <= lo2:
            return 0.0
        FU = F(U)
        g = lambda b2: f(b2) * max(0.0, FU - F(max(0.0, 1 - 1 / (4 * (1 - b2)))))
        return f(b1) * quad(g, lo2, hi2, epsabs=0, epsrel=1e-11, limit=200)[0]
    return quad(inner, 0.5 - W, 0.5 + W, points=[0.5], epsabs=0, epsrel=1e-10, limit=400)[0]


def hdp_route2(alpha):
    """The same probability in logit coordinates, density exp(-a g(l))/Z with g(l) = 2 log cosh(l/2)."""
    a = alpha / 3.0
    logZ = a * np.log(4.0) + 2 * gammaln(a) - gammaln(2 * a)
    W = 16 * np.sqrt(2.0 / a)
    X, Wt = np.polynomial.legendre.leggauss(40)
    g = lambda l: np.abs(l) + 2 * np.log1p(np.exp(-np.abs(l))) - 2 * np.log(2.0)
    dens = lambda l: np.exp(-a * g(l) - logZ)
    sig = lambda l: 1 / (1 + np.exp(-l))
    logit = lambda b: np.log(b) - np.log1p(-b)

    def inner_l2(B1, B3):
        lo, hi = 1 - 1 / (4 * (1 - B3)), 1 / (4 * B1)
        l_lo = -np.inf if lo <= 0 else logit(lo)
        l_hi = np.inf if hi >= 1 else logit(hi)
        l_lo, l_hi = max(l_lo, -W), min(l_hi, W)
        if l_hi <= l_lo:
            return 0.0
        m, h = (l_hi + l_lo) / 2, (l_hi - l_lo) / 2
        return h * np.dot(Wt, dens(m + h * X))

    def mid(l1):
        B1 = sig(l1)
        hi3 = min(1.0, 1 / (4 * (1 - B1)))
        lo3 = 0.0 if B1 <= 0.25 else max(0.0, 1 - B1 / (4 * B1 - 1))
        if hi3 <= lo3:
            return 0.0
        l3lo = -W if lo3 <= 0 else max(-W, logit(lo3))
        l3hi = W if hi3 >= 1 else min(W, logit(hi3))
        if l3hi <= l3lo:
            return 0.0
        return dens(l1) * quad(lambda l3: dens(l3) * inner_l2(B1, sig(l3)), l3lo, l3hi, epsabs=0, epsrel=1e-11, limit=200)[0]
    return quad(mid, -W, W, points=[0.0], epsabs=0, epsrel=1e-10, limit=400)[0]


def hdp_quantile(alpha):
    """P(direct) by quadrature in the quantile coordinates u_j = F(B_j), where F is the Beta(a,a) cdf.
    For fixed B_1 the event in B_3 is an interval [Lo(B_2), U(B_1)], so B_3 is integrated exactly."""
    a = alpha / 3.0
    F = lambda b: float(betainc(a, a, b))
    Finv = lambda u: float(betaincinv(a, a, u))
    F34 = F(0.75)

    def inner(u1):
        B1 = Finv(u1)
        U = min(1.0, 1 / (4 * (1 - B1))) if B1 < 1 else 1.0          # (1 - B1) B3 <= 1/4
        FU = F(U) if U < 1 else 1.0
        u2lo = F(max(0.0, 1 - 1 / (4 * (1 - U)))) if U < 1 else 0.0   # Lo(B2) < U
        u2hi = F(min(1.0, 1 / (4 * B1))) if B1 > 0.25 else 1.0        # B1 B2 <= 1/4
        if u2hi <= u2lo:
            return 0.0
        val = FU * max(0.0, u2hi - max(u2lo, F34))                    # Lo(B2) = 0 once B2 >= 3/4
        lo, hi = u2lo, min(F34, u2hi)
        if hi > lo:
            g = lambda u2: FU - F(max(0.0, 1 - 1 / (4 * (1 - Finv(u2)))))
            val += quad(g, lo, hi, epsabs=1e-13, epsrel=1e-10, limit=200)[0]
        return val
    pts = sorted({F(0.25), F(1 / 3), F(2 / 3), F(0.75)})
    return quad(inner, 0, 1, points=pts, epsabs=1e-12, epsrel=1e-10, limit=500)[0]


def check_hdp():
    print('\nProposition 7.4: the direct jump under the sticky HDP prior', flush=True)
    import warnings
    from scipy.integrate import IntegrationWarning
    warnings.simplefilter('ignore', IntegrationWarning)
    rng = np.random.default_rng(20260925)
    M = 10 ** 6
    # the recorded Monte Carlo values (same seed), to 5 decimals; fig_sticky plots them, and the text after Proposition 7.4 quotes omega = 1
    printed = {0.01: '0.24735', 0.1: '0.22516', 1: '0.11530', 3: '0.05339', 10: '0.01883', 30: '0.00663', 100: '0.00201', 1000: '0.00021'}
    mc = {}
    quadv = {}
    for alpha, pr in printed.items():
        a = alpha / 3
        B1, B2, B3 = rng.beta(a, a, size=(3, M))
        P = float(((B1 * B2 <= 0.25) & ((1 - B1) * B3 <= 0.25) & ((1 - B2) * (1 - B3) <= 0.25)).mean())
        mc[alpha] = P
        se = sqrt(max(P * (1 - P), 1e-12) / M)
        qv = hdp_quantile(alpha)
        quadv[alpha] = qv
        ok = abs(P - float(pr)) <= tol_of(pr) + 1e-12 and abs(P - qv) < 4 * se
        check(f'omega = {alpha}: P(direct), Monte Carlo with 10^6 draws', ok,
              f'paper {pr}; Monte Carlo {P:.6f} (s.e. {se:.1e}), quadrature {qv:.6f}, difference {(P - qv) / se:+.1f} s.e.')
    check('omega -> 0: the probability tends to 1/4', abs(quadv[0.01] - 0.25) < 0.005, f'quadrature {quadv[0.01]:.5f} at omega = 0.01')
    agree('omega = 1: P(direct) to 3 digits', '0.115', {'Monte Carlo': mc[1], 'quadrature': quadv[1]})
    agree('omega = 1: prior probability of an intermediate window (1 - P(direct))', '0.88', {'Monte Carlo': 1 - mc[1], 'quadrature': 1 - quadv[1]})
    lim = 3 * sqrt(3) / (8 * pi)
    agree('3 sqrt3/(8 pi)', '0.2067483', {'closed': lim})
    for alpha, pr in ((100, '0.204496'), (300, '0.205981'), (1000, '0.206517'), (3000, '0.206671'), (30000, '0.206741')):
        v1 = alpha * hdp_route1(alpha)
        vals = {'Beta coordinates': v1, 'quantile coordinates': alpha * hdp_quantile(alpha)}
        if alpha in (100, 3000):
            vals['logit coordinates'] = alpha * hdp_route2(alpha)
        agree(f'omega P(direct) at omega = {alpha}', pr, vals, f'; ratio to the limit {v1 / lim:.6f}, 1 - 9/(8 omega) = {1 - 9 / (8 * alpha):.6f}')
    r = [(a * hdp_route1(a) / lim - 1) * a for a in (1000, 3000, 30000)]
    check('the next term looks like 1 - 9/(8 omega) (numerical)', all(abs(x + 9 / 8) < 0.01 for x in r), f'omega (ratio - 1) = {np.round(r, 4)}')
    check('Appendix D constants: log cosh 1 > 0.43 and sech^2(1)/2 > 0.2', math.log(math.cosh(1)) > 0.43 and 0.5 / math.cosh(1) ** 2 > 0.2,
          f'{math.log(math.cosh(1)):.5f}, {0.5 / math.cosh(1) ** 2:.5f}')
    y = np.concatenate([np.linspace(-40, 40, 200001), np.geomspace(1e-6, 1e3, 2000)])
    g = 2 * np.log(np.cosh(np.minimum(np.abs(y), 700) / 2))
    ok = np.all(g <= y * y / 4 + 1e-15) and np.all(g >= y * y / 4 - y ** 4 / 96 - 1e-15) and np.all(g >= 0.1 * np.minimum(y * y, np.abs(y)) - 1e-15)
    check('Appendix D bounds: y^2/4 - y^4/96 <= g(y) <= y^2/4 and g(y) >= 0.1 min(y^2, |y|), g = 2 log cosh(y/2)', bool(ok),
          'on a grid of |y| <= 1000')


# ---------------------------------------------------------------- Part 2: Fisher information

def logW_table(N, jmax=None):
    """log W(N,k,j) for interior k = 1..N-1 and j = 0..jmax (the run count of Paper A)."""
    jmax = N - 1 if jmax is None else min(jmax, N - 1)
    ks = np.arange(1, N)[:, None].astype(float)
    js = np.arange(jmax + 1)[None, :]
    a, b = ks, N - ks
    lC = lambda n, r: np.where((r >= 0) & (r <= n), gammaln(n + 1) - gammaln(np.maximum(r, 0) + 1) - gammaln(np.maximum(n - r, 0) + 1), -np.inf)
    i_odd = (js + 1) // 2
    odd = log(2) + lC(a - 1, i_odd - 1) + lC(b - 1, i_odd - 1)
    i_ev = js // 2
    x1 = lC(a - 1, i_ev) + lC(b - 1, i_ev - 1)
    x2 = lC(a - 1, i_ev - 1) + lC(b - 1, i_ev)
    ev = np.logaddexp(x1, x2)
    out = np.where(js % 2 == 1, odd, ev)
    out[:, 0] = -np.inf
    return out


def fisher_A(N, q, jmax=None):
    """Method A: e_N(q) = Var(E[J|K]) / Var J from the run formula; also the joint pieces."""
    p = 1 - q
    LW = logW_table(N, jmax)
    js = np.arange(LW.shape[1], dtype=float)
    T = LW + js * log(q / p)
    mx = T.max(1, keepdims=True)
    E = np.exp(T - mx)
    S = E.sum(1)
    EJ = (E * js).sum(1) / S
    Pint = np.exp(log(0.5) + (N - 1) * log(p) + mx[:, 0] + np.log(S))
    Patom = 0.5 * p ** (N - 1)
    mean = (N - 1) * q
    var = 2 * Patom * mean ** 2 + (Pint * (EJ - mean) ** 2).sum()
    PK = np.concatenate([[Patom], Pint, [Patom]])
    EJK = np.concatenate([[0.0], EJ, [0.0]])
    return var / ((N - 1) * p * q), PK, EJK


def fisher_B(N, q):
    """Method B: Fisher information of K from the recurrence, derivative by the complex step."""
    eps = 1e-30
    P = paperA_law(N, complex(q, eps))
    dP = P.imag / eps
    P0 = P.real
    IK = float(np.sum(dP[P0 > 0] ** 2 / P0[P0 > 0]))
    return IK * q * (1 - q) / (N - 1)


def R2_numeric(N, q, PK, EJK):
    X2 = (2.0 * np.arange(N + 1) - N) ** 2
    mean = (N - 1) * q
    c = (PK * (X2 - (PK * X2).sum()) * (EJK - mean)).sum()
    v = (PK * (X2 - (PK * X2).sum()) ** 2).sum()
    return c * c / (v * (N - 1) * q * (1 - q))


def R2_closed(N, q):
    p = 1 - q
    r = 1 - 2 * q
    x = N * q
    rN = r ** N
    V = 1 - (1 + 8 * r + r * r + 8 * r ** (N + 1)) / (4 * p * x) + r * (1 - rN) * (2 * (1 + 2 * r) * (2 + r) - r * (1 - rN)) / (8 * p * p * x * x)
    return (1 + rN - p * (1 - rN) / x) ** 2 / (V * 2 * (N - 1) * p * q)


_EINF = {}


def e_inf(x, dps=20):
    """Telegraph limit of e_N(x/N) (an open question in Section 9), by quadrature of the Bessel density."""
    if (x, dps) not in _EINF:
        _EINF[(x, dps)] = _e_inf(x, dps)
    return _EINF[(x, dps)]


def _e_inf(x, dps):
    with mp.workdps(dps):
        x = mp.mpf(x)

        def parts(y):
            c = mp.sqrt(y * (1 - y))
            t = 2 * x * c
            I0, I1 = mp.besseli(0, t), mp.besseli(1, t)
            g = x * I0 + x * I1 / (2 * c)
            dg = I0 + x * 2 * c * I1 + I1 / (2 * c) + x * (I0 - I1 / t)
            return mp.e ** (-x) * g, x * dg / g
        pts = [0, mp.mpf(1) / 4, mp.mpf(1) / 2, mp.mpf(3) / 4, 1]
        mass = mp.quad(lambda y: parts(y)[0], pts) + mp.e ** (-x)
        var = mp.quad(lambda y: (lambda f, EJ: f * (EJ - x) ** 2)(*parts(y)), pts) + mp.e ** (-x) * x * x
        return float(var / x), float(mass)


def check_moments():
    print('\nLemma E.1 (exact moments, q symbolic, N = 1..12) and Lemma E.4(b)', flush=True)
    q = sp.symbols('q', positive=True)
    Ns, R = sp.symbols('N R')
    p = 1 - q
    rho = 1 - 2 * q

    def closed(Nv, Rv):              # Rv stands for rho^N; the forms are copied from Lemma E.1
        EX2 = Nv * p / q - rho * (1 - Rv) / (2 * q ** 2)
        Cov = -p / q ** 2 * (Nv * q * (1 + Rv) - p * (1 - Rv))
        EX4 = (3 * Nv ** 2 * p ** 2 / q ** 2 - Nv * p * (1 + 10 * rho + rho ** 2) / (2 * q ** 3)
               + rho * (1 + 2 * rho) * (2 + rho) * (1 - Rv) / (2 * q ** 4) - 3 * Nv * p * rho * Rv / q ** 3)
        return EX2, Cov, EX4
    state = {(1, 1, 0): sp.Rational(1, 2), (-1, -1, 0): sp.Rational(1, 2)}
    bad = 0
    for Nv in range(1, 13):
        if Nv > 1:
            new = {}
            for (e, X, J), pr in state.items():
                for e2, w, dj in ((e, p, 0), (-e, q, 1)):
                    key = (e2, X + e2, J + dj)
                    new[key] = new.get(key, 0) + pr * w
            state = {k: sp.expand(v) for k, v in new.items()}
        EX2 = sp.expand(sum(pr * X ** 2 for (e, X, J), pr in state.items()))
        EX4 = sp.expand(sum(pr * X ** 4 for (e, X, J), pr in state.items()))
        EJX2 = sp.expand(sum(pr * J * X ** 2 for (e, X, J), pr in state.items()))
        EJ = sp.expand(sum(pr * J for (e, X, J), pr in state.items()))
        c2, cc, c4 = closed(Nv, rho ** Nv)
        diffs = [sp.simplify(EX2 - c2), sp.simplify(EX4 - c4), sp.simplify(EJX2 - EJ * EX2 - cc), sp.simplify(EJ - (Nv - 1) * q)]
        bad += any(dd != 0 for dd in diffs)
    check('E X^2, Cov(J, X^2), E X^4 of Lemma E.1 at N = 1..12 (exact, q symbolic)', bad == 0, f'{bad} mismatches')
    EX2, Cov, EX4 = closed(Ns, R)
    x = Ns * q
    V = 1 - (1 + 8 * rho + rho ** 2 + 8 * rho * R) / (4 * p * x) + rho * (1 - R) * (2 * (1 + 2 * rho) * (2 + rho) - rho * (1 - R)) / (8 * p ** 2 * x ** 2)
    id1 = sp.simplify(sp.together(EX4 - EX2 ** 2 - 2 * Ns ** 2 * p ** 2 * V / q ** 2))
    id2 = sp.simplify(sp.together(Cov ** 2 / ((Ns - 1) * p * q * (EX4 - EX2 ** 2)) - (1 + R - p * (1 - R) / x) ** 2 / (2 * (Ns - 1) * p * q * V)))
    check('Var X^2 = 2N^2p^2V/q^2 and the closed form of R^2_N (identities in N, q, rho^N)', id1 == 0 and id2 == 0, f'differences {id1}, {id2}')
    # method B: exact rationals at other N and q, straight from the words
    bad = 0
    for Nv in (13, 15, 17):
        for qv in (Fraction(1, 7), Fraction(2, 5), Fraction(3, 4)):
            pv = 1 - qv
            law = {(1, 1, 0): Fraction(1, 2), (-1, -1, 0): Fraction(1, 2)}
            for _ in range(Nv - 1):
                new = {}
                for (e, X, J), pr in law.items():
                    for e2, w, dj in ((e, pv, 0), (-e, qv, 1)):
                        new[(e2, X + e2, J + dj)] = new.get((e2, X + e2, J + dj), 0) + pr * w
                law = new
            EX2v = sum(pr * X ** 2 for (e, X, J), pr in law.items())
            EX4v = sum(pr * X ** 4 for (e, X, J), pr in law.items())
            qs = sp.Rational(qv.numerator, qv.denominator)
            c2, cc, c4 = [sp.simplify(t.subs({Ns: Nv, R: (1 - 2 * qs) ** Nv, q: qs})) for t in closed(Ns, R)]
            bad += (sp.Rational(EX2v.numerator, EX2v.denominator) != c2) + (sp.Rational(EX4v.numerator, EX4v.denominator) != c4)
    check('Lemma E.1 in exact rational arithmetic at N = 13, 15, 17 and 3 values of q', bad == 0, f'{bad} mismatches')
    EW4f = sp.lambdify((Ns, R, q), EX4 / Ns ** 4, 'math')
    EW4 = lambda Nv, qv: EW4f(Nv, (1 - 2 * qv) ** Nv, qv)
    worst = max(EW4(Nv, qv) - (3 * (1 - qv) ** 2 / (Nv * qv) ** 2 + 9 / (2 * (Nv * qv) ** 4))
                for Nv in (5, 20, 100, 1000) for qv in np.linspace(0.001, 0.5, 60))
    check('Lemma E.4(b): E W^4 <= 3p^2/x^2 + 9/(2x^4) for q <= 1/2', worst <= 1e-12, f'max of left minus right {worst:.2e}')
    with mp.workdps(30):
        ts = [mp.mpf(10) ** (k / 4) for k in range(-16, 17)]
        ok = all(mp.besseli(1, t) / mp.besseli(0, t) >= (mp.sqrt(1 + t * t) - 1) / t and mp.besseli(1, t) < mp.besseli(0, t) for t in ts)
    check('Lemma E.3: (sqrt(1+t^2) - 1)/t <= I_1(t)/I_0(t) < 1', ok, 't from 1e-4 to 1e4')


def check_fisher(full):
    print('\nPropositions 8.1, 8.2, Theorem 8.3 and Table 3: the endpoint efficiency', flush=True)
    # small cases in exact arithmetic
    worst = 0.0
    for N in (3, 5, 8, 12, 14):
        for qv in (Fraction(1, 10), Fraction(1, 3), Fraction(3, 5)):
            p = 1 - qv
            P = [Fraction(0)] * (N + 1)
            dP = [Fraction(0)] * (N + 1)
            JK = [Fraction(0)] * (N + 1)
            for w in range(2 ** N):
                bits = [(w >> i) & 1 for i in range(N)]
                k = sum(bits)
                j = sum(bits[i] != bits[i + 1] for i in range(N - 1))
                r = N - 1 - j
                pr = Fraction(1, 2) * p ** r * qv ** j
                P[k] += pr
                dP[k] += Fraction(1, 2) * ((j * qv ** (j - 1) * p ** r if j else 0) - (r * p ** (r - 1) * qv ** j if r else 0))
                JK[k] += j * pr
            e1 = sum(dP[k] ** 2 / P[k] for k in range(N + 1)) * p * qv / (N - 1)
            EJ = sum(JK)
            e2 = (sum(JK[k] ** 2 / P[k] for k in range(N + 1)) - EJ ** 2) / ((N - 1) * p * qv)
            worst = max(worst, abs(float(e1 - e2)), abs(fisher_A(N, float(qv))[0] - float(e1)), abs(fisher_B(N, float(qv)) - float(e1)))
    check('Proposition 8.1 (exact, all 2^N words) and both methods agree to 15 digits, N <= 14', worst < 1e-14, f'max difference {worst:.1e}')
    # 30-digit arithmetic at larger N (the run formula of Paper A in mpmath)
    worst = 0.0
    for N, qv in ((100, 0.035), (400, 0.0119), (400, 0.1)):
        with mp.workdps(30):
            q = mp.mpf(qv)
            p = 1 - q
            u = q / p
            mean = (N - 1) * q
            var = p ** (N - 1) * mean ** 2
            for k in range(1, N):
                a, b = k, N - k
                S = SJ = mp.mpf(0)
                for j in range(1, N):
                    if j % 2:
                        i = (j + 1) // 2
                        W = 2 * mp.binomial(a - 1, i - 1) * mp.binomial(b - 1, i - 1)
                    else:
                        i = j // 2
                        W = mp.binomial(a - 1, i) * mp.binomial(b - 1, i - 1) + mp.binomial(a - 1, i - 1) * mp.binomial(b - 1, i)
                    if W:
                        t = W * u ** j
                        S += t
                        SJ += j * t
                        if j > 4 * N * qv + 40 and t < S * mp.mpf(10) ** -40:
                            break
                var += p ** (N - 1) / 2 * S * (SJ / S - mean) ** 2
            e30 = float(var / ((N - 1) * p * q))
        worst = max(worst, abs(fisher_A(N, qv)[0] / e30 - 1), abs(fisher_B(N, qv) / e30 - 1))
    check('both methods agree with 30-digit arithmetic at N = 100 and 400', worst < 1e-13, f'max relative difference {worst:.1e}')
    bad = 0
    for N in (3, 5, 10, 50, 200):
        for qv in (0.001, 0.01, 0.05, 0.2, 0.5, 0.8):
            e = fisher_A(N, qv)[0]
            p = 1 - qv
            chain = [1 - (N - 2) * qv, p ** (N - 2), (N - 1) * qv * p ** (N - 2) / (1 - p ** (N - 1)), e, 1 - (N - 2) * qv * p ** (N - 3) / (2 * p + (N - 2) * qv)]
            bad += any(chain[i] > chain[i + 1] + 1e-12 for i in range(4))
    ex = fisher_A(10, 0.05)[0]
    check('Remark 8.2: the chain of inequalities', bad == 0, f'{bad} violations in 30 cases; at (N, q) = (10, 0.05) e = {ex:.8f}')
    slopes = [(fisher_A(20, qq)[0] - 1 + 18 * qq / 2) / qq ** 2 for qq in (1e-2, 5e-3, 2.5e-3)]
    check('e_N(q) = 1 - (N-2)q/2 + O(q^2) at fixed N', np.ptp(slopes) < 0.1 * abs(slopes[0]) + 1, f'(e - 1 + (N-2)q/2)/q^2 = {np.round(slopes, 3)} at N = 20')
    # Theorem 8.3: e >= R^2 and the closed form of R^2
    worst = 0.0
    bad = 0
    for N in (20, 100, 500):
        for qv in (0.01, 0.05, 0.2, 0.45, 0.7):
            e, PK, EJK = fisher_A(N, qv)
            r2n = R2_numeric(N, qv, PK, EJK)
            worst = max(worst, abs(r2n / R2_closed(N, qv) - 1))
            bad += e < r2n - 1e-12
    check('Theorem 8.3: closed form of R^2_N = numeric R^2 from the exact law, and e_N >= R^2_N', worst < 1e-8 and bad == 0,
          f'max relative difference {worst:.1e}, {bad} violations')
    # Table 3
    table = {50: ('2.8998', '0.24117', '1.3987', '1.8869', '0.20873', '0.20216'),
             100: ('3.5034', '0.18869', '1.3221', '1.7379', '0.16642', '0.16309'),
             200: ('4.1220', '0.15242', '1.2565', '1.6151', '0.13767', '0.13602'),
             400: ('4.7501', '0.12681', '1.2047', '1.5196', '0.11715', '0.11634'),
             800: ('5.3849', '0.10823', '1.1656', '1.4470', '0.10187', '0.10147'),
             1600: ('6.0246', '0.09433', '1.1366', '1.3919', '0.09007', '0.08988'),
             3200: ('6.6684', '0.08361', '1.1151', '1.3496', '0.08070', '0.08060')}
    eN = {}
    for N, row in table.items():
        uA = uN_runs(N)
        uB = uN_dp(N)
        qA, qB = uA / (1 + uA), uB / (1 + uB)
        eA, PK, EJK = fisher_A(N, qA, jmax=min(N - 1, 400))
        eB = fisher_B(N, qB)
        eN[N] = eA
        L = log(N)
        xA, xB = N * qA, N * qB
        vals = [({'runs': xA, 'recurrence': xB}), {'A': eA, 'B': eB}, {'A': 2 * xA * eA, 'B': 2 * xB * eB},
                {'A': 2 * L * eA, 'B': 2 * L * eB}, {'numeric': R2_numeric(N, qA, PK, EJK), 'closed': R2_closed(N, qB)},
                {'A': 1 / (2 * xA) + 1 / (4 * xA ** 2), 'B': 1 / (2 * xB) + 1 / (4 * xB ** 2)}]
        names = ['x_N', 'e_N(q_N)', '2 x_N e_N', '2 L e_N', 'R^2_N(q_N)', '1/(2x) + 1/(4x^2)']
        for nm, pr, v in zip(names, row, vals):
            agree(f'Table 3, N = {N}: {nm}', pr, v)
    agree('2 e_N log N at N = 100', '1.74', {'A': 2 * log(100) * eN[100]})
    agree('2 e_N log N at N = 3200', '1.35', {'A': 2 * log(3200) * eN[3200]})
    rem = []
    for N in table:
        L = log(N)
        rem.append((eN[N] - 1 / (2 * L) - (log(L) + 1 + log(8 / pi)) / (4 * L * L)) * L ** 3 / log(L) ** 2)
    check('Corollary 8.4: the remainder is O((log L)^2/L^3) along Table 3', max(abs(r) for r in rem) < 10, f'remainder L^3/(log L)^2 = {np.round(rem, 3)}')
    # fixed q (an open question in Section 9)
    for N, pr in ((400, '1.0113'), (800, '1.0055'), (1600, '1.0027')):
        qv = 0.1
        agree(f'fixed q = 0.1, N = {N}: 2(N-1)pq e_N', pr, {'A': 2 * (N - 1) * 0.9 * 0.1 * fisher_A(N, qv)[0], 'B': 2 * (N - 1) * 0.09 * fisher_B(N, qv)})
    # the telegraph limit
    eis = {}
    for x, pr in ((1, '1.18'), (2, '1.40'), (3, '1.34')):
        ei, mass = e_inf(x)
        eis[x] = ei
        # the discrete efficiency at fixed x = Nq, extrapolated in 1/N (the limit is not proved, so this is numerical)
        Ns = (8000, 16000) if full else (4000, 8000)
        eA, eB = (fisher_B(N, x / N) for N in Ns)
        vals = {'telegraph': 2 * x * ei, f'discrete, N = {Ns[0]}, {Ns[1]} extrapolated': 2 * x * (2 * eB - eA)}
        agree(f'2x e_inf(x) at x = {x}', pr, vals, f'; total mass - 1 = {mass - 1:.0e}')
    xs = [1.5, 1.8, 2.0, 2.2, 2.5]
    vals = [2 * x * e_inf(x, 20)[0] for x in xs]
    check('2x e_inf(x) peaks near 1.40 around x = 2', max(vals) < 1.41 and abs(xs[int(np.argmax(vals))] - 2) <= 0.2, f'{np.round(vals, 4)} at x = {xs}')
    check('2x e_inf(x) tends to 1', abs(2 * 50 * e_inf(50)[0] - 1) < 0.02, f'{2 * 50 * e_inf(50)[0]:.4f} at x = 50')
    for N, pr in ((100, '1.025'), (3200, '1.002')):
        u = uN_runs(N)
        x = N * u / (1 + u)
        agree(f'e_N(q_N)/e_inf(x_N) at N = {N}', pr, {'ratio': eN[N] / e_inf(x)[0]})


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--full', action='store_true', help='also run the larger cells')
    args = parser.parse_args()
    t0 = time.time()
    for step in (check_kernels, lambda: check_sticky_switches(args.full), check_sticky_masses, check_hdp, check_moments,
                 lambda: check_fisher(args.full)):
        t1 = time.time()
        step()
        print(f'  ({time.time() - t1:.0f} s)', flush=True)
    print(f'\nverify_sticky_fisher: {len(FAILS)} failures, {time.time() - t0:.0f} s', flush=True)
    if FAILS:
        print('failed: ' + '; '.join(FAILS))
        sys.exit(1)


if __name__ == '__main__':
    main()
