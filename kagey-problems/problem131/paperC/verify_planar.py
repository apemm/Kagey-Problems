"""Checks for Section 6 and Appendix C of Paper C (the planar persistent walk).

The walk has directions E, N, W, S. At each step it keeps its direction with
probability p_0 = 1 - beta h, turns left or right with probability r h each and
reverses with probability s h, where beta = 2r + s. The first direction is
uniform. c_N is the probability of the corner N e_E and o_N that of the origin.

We compute o_N in 4 ways.
Method A (Lemma 6.1). The number m of switches is binomial, the skeleton is a
random walk on Z_4, and the run lengths are uniform over the compositions. The
expected number of compositions that return to the origin is tabulated once per
N and (r, s), so a root in h is cheap. The tables are written as matrix
products, which makes N = 10240 feasible.
Method B (Fourier inversion). In the coordinates U = Y_1 + Y_2, V = Y_1 - Y_2
each step flips the sign of U, of V, of both, or of neither, independently of
the past, so o_N is a 2-dimensional Fourier integral of a 4 x 4 matrix power.
With K >= N + 1 points per circle the trapezoid rule is exact.
For N <= 10 both are compared with a direct dynamic program and with all 4^N words.
Paper A's crossing N(1 - p_N) is found from the run formula and from Paper A's
recurrence (imported from verify_sticky_fisher.py).

Run with python -B verify_planar.py, or add --full for N = 1280, ..., 10240
(method A everywhere and method B up to N = 2560).
"""
import argparse
import itertools
import sys
import time
from fractions import Fraction
from math import comb, exp, log, log1p, pi, sqrt

import numpy as np
from scipy.optimize import brentq
from scipy.special import gammaln
from scipy.stats import binom

from verify_sticky_fisher import logS, uN_dp, uN_runs

FAILS = []
STEPS = [(1, 0), (0, 1), (-1, 0), (0, -1)]


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
    ok = all(abs(float(v) - target) <= t for v in values.values())
    shown = ', '.join(f'{k} {float(v):.10g}' for k, v in values.items())
    check(label, ok, f'paper {printed}; {shown}{extra}')


def log_corner(N, r, s, h):
    return log(0.25) + (N - 1) * log1p(-(2 * r + s) * h)


# ---------------------------------------------------------------- method A: three levels

def skeleton_law(r, s, Mmax):
    """For m = 0..Mmax, the law of (a, b, c, d) = numbers of E, W, N, S runs of a skeleton with m
    switches, started at E (every quantity below is invariant under the rotations, so this equals
    the uniform start). Returned as dense arrays P[m][a, b, c] with d = m + 1 - a - b - c."""
    beta = 2 * r + s
    moves = [(1, r / beta), (-1, r / beta), (2, s / beta)]
    S = Mmax + 2
    cur = np.zeros((4, S, S, S))
    cur[0, 1, 0, 0] = 1.0
    out = [cur.sum(0).copy()]
    for _ in range(Mmax):
        new = np.zeros_like(cur)
        for z in range(4):
            for dz, p in moves:
                if p == 0:
                    continue
                z2 = (z + dz) % 4
                if z2 == 0:
                    new[z2, 1:, :, :] += p * cur[z][:-1, :, :]
                elif z2 == 2:
                    new[z2, :, 1:, :] += p * cur[z][:, :-1, :]
                elif z2 == 1:
                    new[z2, :, :, 1:] += p * cur[z][:, :, :-1]
                else:
                    new[z2] += p * cur[z]
        cur = new
        out.append(cur.sum(0).copy())
    return out


def threelevel_tables(N, skel):
    """E0[m], E4[m]: expected number of run-length compositions that end at the origin, divided by
    C(N-1, m), for the skeletons on one axis (E0) and with all 4 directions (E4)."""
    assert N % 2 == 0
    n = N // 2
    Mmax = len(skel) - 1
    lCm = gammaln(N) - gammaln(np.arange(Mmax + 1) + 1) - gammaln(N - np.arange(Mmax + 1))
    E0 = np.zeros(Mmax + 1)
    E4 = np.zeros(Mmax + 1)
    X = np.arange(1, n, dtype=float)                 # E steps = W steps = X, N steps = S steps = n - X
    Y = n - X
    ks = np.arange(1, Mmax + 2)
    # Fh[k, X] = C(X-1, k-1) (k-1)! / X^(k-1), which lies in [0, 1]
    okF = X[None, :] >= ks[:, None]
    okG = Y[None, :] >= ks[:, None]
    lF = gammaln(X[None, :]) - gammaln(np.maximum(X[None, :] - ks[:, None] + 1, 1)) - (ks[:, None] - 1) * np.log(X[None, :])
    lG = gammaln(Y[None, :]) - gammaln(np.maximum(Y[None, :] - ks[:, None] + 1, 1)) - (ks[:, None] - 1) * np.log(Y[None, :])
    Fh = np.where(okF, np.exp(np.where(okF, lF, 0)), 0.0)
    Gh = np.where(okG, np.exp(np.where(okG, lG, 0)), 0.0)
    lfact = gammaln(ks)                              # log (k-1)!
    logX, logY = np.log(X), np.log(Y)
    for m in range(0, min(Mmax, N - 1) + 1):
        P = skel[m]
        # one axis: E/W only (c = d = 0, X = n) or N/S only (a = b = 0, X = 0)
        tot0 = 0.0
        for a in range(0, m + 2):
            b = m + 1 - a
            for (pa, pb, pc) in ((a, b, 0), (0, 0, a)):
                if max(pa, pb, pc) >= P.shape[0]:
                    continue
                p = P[pa, pb, pc]
                if p == 0:
                    continue
                k1, k2 = (a, b)
                if k1 == 0 or k2 == 0 or k1 > n or k2 > n:
                    continue
                tot0 += p * exp(2 * gammaln(n) - gammaln(k1) - gammaln(n - k1 + 1) - gammaln(k2) - gammaln(n - k2 + 1) - lCm[m])
        E0[m] = tot0
        if m < 3 or n < 2:
            continue
        # all 4 directions: a + b = s_, c + d = t_ = m + 1 - s_, every count >= 1
        logs = []
        for s_ in range(2, m):
            t_ = m + 1 - s_
            A_idx = [(a, s_ - a) for a in range(1, s_)]
            C_idx = [(c, t_ - c) for c in range(1, t_)]
            Pm = np.array([[P[a, b, c] for (c, d) in C_idx] for (a, b) in A_idx])
            if not Pm.any():
                continue
            wA = np.array([lfact[a - 1] + lfact[b - 1] for a, b in A_idx])
            wC = np.array([lfact[c - 1] + lfact[d - 1] for c, d in C_idx])
            with np.errstate(divide='ignore'):
                lPm = np.log(Pm) - wA[:, None] - wC[None, :]
            shift = np.max(lPm[np.isfinite(lPm)])
            Pt = np.exp(lPm - shift)
            FF = np.array([Fh[a - 1] * Fh[b - 1] for a, b in A_idx])
            GG = np.array([Gh[c - 1] * Gh[d - 1] for c, d in C_idx])
            v = np.einsum('ax,ax->x', FF, Pt @ GG)
            ok = v > 0
            if ok.any():
                logs.append(np.log(v[ok]) + shift + (s_ - 2) * logX[ok] + (t_ - 2) * logY[ok] - lCm[m])
        if logs:
            allv = np.concatenate(logs)
            mx = allv.max()
            E4[m] = exp(mx) * np.exp(allv - mx).sum()
    return E0, E4


class ThreeLevel:
    def __init__(self, N, r, s, Mmax=70):
        self.N, self.r, self.s = N, r, s
        self.E0, self.E4 = threelevel_tables(N, skeleton_law(r, s, Mmax))
        self.Mmax = Mmax

    def parts(self, h):
        """(axis part, four-direction part, tail bound) of o_N."""
        N = self.N
        q = (2 * self.r + self.s) * h
        w = binom.pmf(np.arange(self.Mmax + 1), N - 1, q)
        return float(w @ self.E0), float(w @ self.E4), float(binom.sf(self.Mmax, N - 1, q))

    def crossing(self):
        N, r, s = self.N, self.r, self.s
        beta = 2 * r + s
        f = lambda T: log(sum(self.parts(T / N)[:2])) - log_corner(N, r, s, T / N)
        Tg = 2 * log(N) / beta
        return brentq(f, 0.2 * Tg, 1.5 * Tg, xtol=1e-13, rtol=1e-14)


# ---------------------------------------------------------------- method B: Fourier inversion in the sign basis

def origin_fourier(N, r, s, h, chunk=400000):
    K = N + 1 if (N + 1) % 2 == 1 else N + 2
    p0 = 1 - (2 * r + s) * h
    F = np.zeros((4, 4))                              # states (sign of U, sign of V)
    for iu in range(2):
        for iv in range(2):
            a = 2 * iu + iv
            F[a, a] += p0
            F[a, 2 * (1 - iu) + iv] += r * h
            F[a, 2 * iu + (1 - iv)] += r * h
            F[a, 2 * (1 - iu) + (1 - iv)] += s * h
    half = (K - 1) // 2
    idx = np.arange(half + 1)
    wts = np.where(idx == 0, 1.0, 2.0)                # the integrand is even in each angle
    th = 2 * np.pi * idx / K
    T1, T2 = np.meshgrid(th, th, indexing='ij')
    W12 = np.outer(wts, wts).ravel()
    T1, T2 = T1.ravel(), T2.ravel()
    su = np.array([1, 1, -1, -1])
    sv = np.array([1, -1, 1, -1])
    total = 0.0
    for c0 in range(0, T1.size, chunk):
        ph = np.exp(1j * (T1[c0:c0 + chunk, None] * su[None, :] + T2[c0:c0 + chunk, None] * sv[None, :]))
        M = F[None, :, :] * ph[:, None, :]
        vec = 0.25 * ph
        e = N - 1
        while e > 0:
            if e & 1:
                vec = np.einsum('ga,gab->gb', vec, M)
            e >>= 1
            if e:
                M = M @ M
        total += float((vec.sum(axis=1).real * W12[c0:c0 + chunk]).sum())
    return total / (K * K)


# ---------------------------------------------------------------- small N

def origin_dp(N, r, s, h):
    beta = 2 * r + s
    prob = {0: 1 - beta * h, 1: r * h, 3: r * h, 2: s * h}
    cur = {(d, STEPS[d][0], STEPS[d][1]): 0.25 for d in range(4)}
    for _ in range(N - 1):
        nxt = {}
        for (d, x, y), p in cur.items():
            for e in range(4):
                key = (e, x + STEPS[e][0], y + STEPS[e][1])
                nxt[key] = nxt.get(key, 0.0) + p * prob[(e - d) % 4]
        cur = nxt
    return sum(p for (d, x, y), p in cur.items() if x == 0 and y == 0)


def brute_exact(N, r, s, h):
    """All 4^N words in exact arithmetic: o_N, its axis and 4-direction parts, and Lemma 6.1 word by word."""
    beta = 2 * r + s
    p0 = 1 - beta * h
    q = {0: p0, 1: r * h, 3: r * h, 2: s * h}
    o = o0 = o4 = Fraction(0)
    lemma_ok = True
    for w in itertools.product(range(4), repeat=N):
        pr = Fraction(1, 4)
        for a, b in zip(w, w[1:]):
            pr *= q[(b - a) % 4]
        m = sum(a != b for a, b in zip(w, w[1:]))
        skel = [w[0]] + [b for a, b in zip(w, w[1:]) if a != b]
        skp = Fraction(1, 4)
        for a, b in zip(skel, skel[1:]):
            skp *= (r / beta) if (b - a) % 4 in (1, 3) else (s / beta)
        lemma_ok &= comb(N - 1, m) * (beta * h) ** m * p0 ** (N - 1 - m) * skp / comb(N - 1, m) == pr
        if sum(STEPS[d][0] for d in w) == 0 and sum(STEPS[d][1] for d in w) == 0:
            o += pr
            if set(w) <= {0, 2} or set(w) <= {1, 3}:
                o0 += pr
            else:
                o4 += pr
    return o, o0, o4, lemma_ok


# ---------------------------------------------------------------- Paper A

C0 = 0.5 * log(pi / 8)


def A_exp(Lam):
    """Paper A's expansion of N(1 - p_N) with L replaced by Lam."""
    return Lam - 0.5 * log(Lam) + C0 + (0.25 * log(Lam) - 0.5 * C0 + 0.125) / Lam


_NQ = {}


def paperA_nq(N, both=True):
    """N(1 - p_N) from the run formula and (if both) from Paper A's recurrence."""
    if N not in _NQ:
        u = uN_runs(N)
        v = {'runs': N * u / (1 + u)}
        if both:
            u2 = uN_dp(N)
            v['recurrence'] = N * u2 / (1 + u2)
        _NQ[N] = v
    return _NQ[N]


# ======================================================================== checks

def check_small():
    print('\nLemma 6.1 and Proposition 6.2: the engines for N <= 10', flush=True)
    worst = 0.0
    ok_lemma = True
    ok_parts = True
    for (r, s) in [(Fraction(1, 10), Fraction(1)), (Fraction(1), Fraction(1)), (Fraction(1), Fraction(0)), (Fraction(1, 2), Fraction(1))]:
        for N in (2, 4, 6):
            h = Fraction(1, 13)
            o, o0, o4, lem = brute_exact(N, r, s, h)
            ok_lemma &= lem
            c = Fraction(1, 4) * (1 - (2 * r + s) * h) ** (N - 1)
            u = s * h / (1 - (2 * r + s) * h)
            ok_parts &= o0 == 2 * c * S_exact(N, u)
    # the test cells of ledger_C3.md (r, s, h); the reference is the exact sum over words for N <= 8
    for (rf, sf, hh) in ((0.3, 0.7, 0.2), (1.0, 0.0, 0.13), (0.1, 1.0, 0.31)):
        for N in (2, 4, 6, 8, 10):
            a0, a4, _ = ThreeLevel(N, rf, sf, Mmax=N).parts(hh)
            vals = [a0 + a4, origin_fourier(N, rf, sf, hh), origin_dp(N, rf, sf, hh)]
            if N <= 8:
                vals.append(float(brute_exact(N, Fraction(str(rf)), Fraction(str(sf)), Fraction(str(hh)))[0]))
            ref = vals[-1]
            if ref == 0:                              # with turns only, 2 steps cannot return
                worst = max(worst, max(abs(v) for v in vals))
            else:
                worst = max(worst, max(abs(v / ref - 1) for v in vals))
    check('Lemma 6.1: every word has probability Bin(m) x skeleton / C(N-1, m) (exact, N <= 6)', ok_lemma, '')
    check('Proposition 6.2: the axis part is 2 S_N(u) c_N (exact, N <= 6)', ok_parts, '')
    check('three levels = Fourier = dynamic program = all 4^N words (paper: 2e-13)', worst < 2e-13, f'max relative difference {worst:.1e}, N <= 10')


def S_exact(N, u):
    """Paper A's S_N(u) = S_{N/2,N/2}(u), exactly for rational u."""
    a = b = N // 2
    tot = Fraction(0)
    for m1 in range(1, a + 1):
        for m2 in (m1 - 1, m1, m1 + 1):
            if 1 <= m2 <= b:
                tot += (2 if m1 == m2 else 1) * comb(a - 1, m1 - 1) * comb(b - 1, m2 - 1) * u ** (m1 + m2 - 1)
    return tot


def check_bounds():
    print('\nProposition 6.2 and Theorem 6.4(a): the bounds on the 4-direction part', flush=True)
    bad = 0
    worst_id = 0.0
    mono = True
    for (r, s) in [(0.1, 1.0), (0.5, 1.0), (1.0, 1.0), (1.0, 0.0)]:
        beta = 2 * r + s
        for N in (40, 160):
            tl = ThreeLevel(N, r, s)
            prev = -1
            for T in np.linspace(0.3, min(3 * log(N), 0.3 * N / beta), 25):
                h = T / N
                p0 = 1 - beta * h
                a0, a4, tail = tl.parts(h)
                c = exp(log_corner(N, r, s, h))
                u, w = s * h / p0, beta * h / p0
                S = exp(logS(N // 2, N // 2, u)) if s > 0 else 0.0
                worst_id = max(worst_id, abs(a0 / (2 * S * c) - 1) if s > 0 else a0)
                bad += not (0 <= a4 <= w * w / (2 * p0) * (1 - p0 ** N) * (1 + 1e-12))
                bad += not (a4 / c <= 2 * w * w * ((1 + w) ** N - 1) * (1 + 1e-12))
                if s > 0:
                    bad += not (a4 / (2 * S * c) <= w * w * (1 + w) ** N / S * (1 + 1e-12))
                ratio = (a0 + a4) / c
                mono &= ratio > prev
                prev = ratio
    check('axis part = 2 S_N(u) c_N', worst_id < 1e-12, f'max relative difference {worst_id:.1e}')
    check('0 <= o^(4) <= w^2 (1 - p_0^N)/(2 p_0), R_N <= 2w^2((1+w)^N - 1), eps_N <= w^2 (1+w)^N / S_N', bad == 0, f'{bad} violations')
    check('o_N/c_N increases in h (so the crossing is unique)', mono, '25 values of h for each of 8 cells')


def check_crossings(full):
    print('\nTheorem 6.4, Figure 3 and the table of crossings', flush=True)
    pairs = [(0.1, 1.0), (0.3, 1.0), (0.5, 1.0), (1.0, 1.0), (1.0, 0.0)]
    # T* and the zero-turn share 2 S_N(u*) as recorded in ledger_C3.md (the data of Figure 3)
    Nall = (40, 80, 160, 320, 640, 1280, 2560, 5120, 10240)
    recorded = {(1.0, 0.0, 40): '2.6427593', (1.0, 0.0, 80): '3.2524385', (1.0, 0.0, 160): '3.8810744', (1.0, 0.0, 320): '4.5189207',
                (1.0, 0.0, 640): '5.1612511', (1.0, 0.0, 1280): '5.80620711', (1.0, 0.0, 2560): '6.45327647',
                (1.0, 0.0, 5120): '7.10244442', (1.0, 0.0, 10240): '7.75380015', (0.1, 1.0, 640): '4.5482653'}
    for (r, s), vals in {(0.3, 1.0): ('2.0493720', '2.6254217', '3.2329623', '3.8591484', '4.4959627'),
                         (0.5, 1.0): ('1.921659', '2.474789', '3.062736', '3.672591', '4.2960095', '4.92810714', '5.56619750', '6.20883595', '6.85521855'),
                         (1.0, 1.0): ('1.523236', '1.938717', '2.372095', '2.813578', '3.2577636', '3.70221925', '4.14615113', '4.58951666', '5.03254083'),
                         (0.1, 1.0): ('2.137184', '2.709238', '3.307795', '3.922798', '4.5482653', '5.18087744', '5.81884636', '6.46117995', '7.10727127')}.items():
        for N, v in zip(Nall, vals):
            recorded[(r, s, N)] = v
    # the zero-turn share 2 S_N(u*); from N = 1280 on the ledger records S_N(u*) itself, marked 'S'
    shares = {}
    for (r, s), vals in {(0.1, 1.0): ('0.98627', '0.98861', '0.99126', '0.99366', '0.9955879',
                                      ('0.49851428', 'S'), ('0.49902412', 'S'), ('0.49937155', 'S'), ('0.49960168', 'S')),
                         (0.3, 1.0): ('0.9285153', '0.9298968', '0.9355268', '0.9434387', '0.9521065'),
                         (0.5, 1.0): ('0.81799', '0.79678', '0.78263', '0.77379', '0.7686739',
                                      ('0.38301378', 'S'), ('0.38245982', 'S'), ('0.38235717', 'S'), '0.7650'),
                         (1.0, 1.0): ('0.49419', '0.41262', '0.34317', '0.28431', '0.2346652',
                                      ('0.09648150', 'S'), ('0.07905091', 'S'), ('0.06455176', 'S'), '0.1051')}.items():
        for N, v in zip(Nall, vals):
            shares[(r, s, N)] = v
    tableA = {40: ('2.137184', '-0.5729', '-0.5992'), 80: ('2.709238', '-0.5978', '-0.6141'), 160: ('3.307795', '-0.6138', '-0.6249'),
              320: ('3.922798', '-0.6243', '-0.6331'), 640: ('4.548265', '-0.6317', '-0.6395'), 1280: ('5.180877', '-0.6373', '-0.6447'),
              2560: ('5.818846', '-0.6419', '-0.6490'), 5120: ('6.461180', '-0.6458', '-0.6526'), 10240: ('7.107271', '-0.6493', '-0.6556')}
    Gdiff = {40: '-0.0539', 80: '-0.0453', 160: '-0.0343', 320: '-0.0235', 640: '-0.0146'}
    Ns = (40, 80, 160, 320, 640, 1280, 2560, 5120, 10240) if full else (40, 80, 160, 320, 640)
    Tstar = {}
    for N in Ns:
        for (r, s) in pairs:
            if N > 640 and (r, s) == (0.3, 1.0):
                continue
            tl = ThreeLevel(N, r, s)
            T = tl.crossing()
            Tstar[(r, s, N)] = T
            h = T / N
            beta = 2 * r + s
            a0, a4, tail = tl.parts(h)
            c = exp(log_corner(N, r, s, h))
            if N <= (2560 if full else 640):
                fo = origin_fourier(N, r, s, h)
                check(f'(r,s) = ({r},{s}), N = {N}: Fourier inversion at the three-level root', abs(fo / c - 1) < 5e-11,
                      f'T* = {T:.8f}, |o_N/c_N - 1| = {abs(fo / c - 1):.1e}, tail/c_N = {tail / c:.0e}')
            if (r, s, N) in recorded:
                agree(f'(r,s) = ({r},{s}), N = {N}: T* (ledger value)', recorded[(r, s, N)], {'three levels': T})
            if (r, s, N) in shares:
                u = s * h / (1 - beta * h)
                S2 = 2 * exp(logS(N // 2, N // 2, u))
                v = shares[(r, s, N)]
                if isinstance(v, tuple):
                    agree(f'(r,s) = ({r},{s}), N = {N}: axis share S_N(u*)', v[0], {'Paper A polynomial': S2 / 2, 'three levels': a0 / (2 * c)})
                else:
                    agree(f'(r,s) = ({r},{s}), N = {N}: zero-turn share 2 S_N(u*)', v, {'Paper A polynomial': S2, 'three levels': a0 / c})
            if (r, s) == (1.0, 0.0):
                check(f'(r,s) = (1,0), N = {N}: zero-turn share is 0', a0 == 0.0, '')
        # Table A, (r, s) = (0.1, 1)
        T = Tstar[(0.1, 1.0, N)]
        nq = paperA_nq(N, both=N <= (10240 if full else 640))
        L = log(N)
        pT, pd, pf = tableA[N]
        agree(f'Table A, N = {N}: s T*', pT, {'three levels': T})
        agree(f'Table A, N = {N}: s T* - N(1 - p_N)', pd, {k: T - v for k, v in nq.items()})
        agree(f'Table A, N = {N}: -log 2 + log 2/(2L)', pf, {'closed': -log(2) + log(2) / (2 * L)})
        if N in Gdiff:
            agree(f'Table A, N = {N}: s T* - A(L - log 2)', Gdiff[N], {'three levels': T - A_exp(L - log(2))})
    lim = 2 * sqrt(2) / (sqrt(2) + sqrt(5))
    agree('limit of the zero-turn share at s = 2r', '0.774852', {'closed': lim})
    check('the share at s = 2r stays below its limit (N = 640)', 2 * exp(logS(320, 320, Tstar[(0.5, 1.0, 640)] / 640 / (1 - 2 * Tstar[(0.5, 1.0, 640)] / 640))) < lim, '')
    # Remark 6.5 (turns only) at the (1,0) crossings
    for N in ((640, 10240) if full else (640,)):
        T = Tstar[(1.0, 0.0, N)]
        h = T / N
        x = h / (1 - 2 * h)
        uN = uN_runs(N)
        nq = N * uN / (1 + uN)
        ratio = x / uN - 1
        bound = pi * log(N) ** 3 / N
        check(f'N = {N}: 1 <= x*/u_N <= 1 + pi (log N)^3/N', 0 <= ratio <= bound, f'x*/u_N - 1 = {ratio:.4e}, bound {bound:.2e}')
        if N == 10240:
            agree('N = 10240: x*/u_N - 1', '4.0e-4', {'three levels': ratio})
            agree('N = 10240: r T* - N(1 - p_N)', '-0.0027', {'three levels': T - nq})
        else:
            agree('N = 640: x*/u_N - 1 (ledger value)', '4.527e-3', {'three levels': ratio})
            agree('N = 640: r T* - N(1 - p_N) (ledger value)', '-0.01870', {'three levels': T - nq})
    return Tstar


def check_pure_turns():
    print('\nRemark 6.5: turns only, in exact arithmetic', flush=True)
    viol = 0
    mism = 0
    for N in range(2, 31, 2):
        for x in (Fraction(1, 20), Fraction(1, 7), Fraction(2, 5), Fraction(1)):
            # S_N(x)^2 counts all pairs of balanced sign words, and Delta_N(x) the pairs whose switch sets meet
            Sx = S_exact(N, x)
            # 45-degree dynamic program: 2 sign walks U and V that never switch at the same step.
            # We start from the signs (+, +) and multiply by 4 for the other starting signs.
            cur = {(1, 1, 1, 1): Fraction(1)}         # (sign of U, sign of V, U, V)
            for _ in range(N - 1):
                nxt = {}
                for (su, sv, U, V), w in cur.items():
                    for fu, fv, wt in ((0, 0, 1), (1, 0, x), (0, 1, x)):
                        su2, sv2 = (-su if fu else su), (-sv if fv else sv)
                        key = (su2, sv2, U + su2, V + sv2)
                        nxt[key] = nxt.get(key, 0) + w * wt
                cur = nxt
            bal = sum(w for (su, sv, U, V), w in cur.items() if U == 0 and V == 0) * 4
            # the same count from the direction DP: o_N/c_N at s = 0 with x = rh/(1-2rh)
            cur2 = {(d, STEPS[d][0], STEPS[d][1]): Fraction(1) for d in range(4)}
            for _ in range(N - 1):
                nxt = {}
                for (d, a, b), w in cur2.items():
                    for e, wt in ((d, 1), ((d + 1) % 4, x), ((d - 1) % 4, x)):
                        key = (e, a + STEPS[e][0], b + STEPS[e][1])
                        nxt[key] = nxt.get(key, 0) + w * wt
                cur2 = nxt
            direct = sum(w for (d, a, b), w in cur2.items() if a == 0 and b == 0)
            mism += bal != direct
            Delta = Sx * Sx - direct
            B = 4 * x ** 2 + 16 * x ** 3 * (1 + x) ** (N - 2) + 16 * (N - 1) * x ** 4 * (1 + x) ** (2 * (N - 2))
            viol += not (4 * x ** 2 <= Delta <= B)
    check('45-degree dynamic program = direction dynamic program (exact, even N <= 30, 4 values of x)', mism == 0, f'{mism} mismatches')
    check('4x^2 <= Delta_N(x) <= 4x^2 + 16x^3(1+x)^(N-2) + 16(N-1)x^4(1+x)^(2(N-2))', viol == 0, f'{viol} violations')


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--full', action='store_true', help='also run N = 1280..10240')
    args = parser.parse_args()
    t0 = time.time()
    for step in (check_small, check_bounds, check_pure_turns, lambda: check_crossings(args.full)):
        t1 = time.time()
        step()
        print(f'  ({time.time() - t1:.0f} s)', flush=True)
    print(f'\nverify_planar: {len(FAILS)} failures, {time.time() - t0:.0f} s', flush=True)
    if FAILS:
        print('failed: ' + '; '.join(FAILS))
        sys.exit(1)


if __name__ == '__main__':
    main()
