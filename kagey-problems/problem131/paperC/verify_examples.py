"""Checks for Sections 3 and 5 of Paper C (the geometry of the winners and the examples).

First order. The exit rate of a face F is lambda_F = -(Perron root of Q_F), and
the winners for a given tau minimize tau lambda_F + |F| - 1 over the admissible
faces. We compute every lambda_F in 2 ways, with numpy in double precision and
with mpmath at 40 digits, and we find the winners in 2 ways. Method A takes the
lower convex hull of the points (|F|-1, mu_s), where mu_s is the least exit rate
of size s. Method B minimizes the cost directly over all faces on a fine grid of
tau and then solves for the switch values between consecutive winners.

Finite N. The exact law of the composition comes from 2 independent codes.
Method A is a dynamic program of the whole chain over all compositions (packed
by rank, and run for a batch of T values at once). Method B computes the maximum
over each face separately with the run expansion of Lemma 2.3 (imported from
verify_second_order.py) and a search over the lattice near its real maximum.
The global mode is the best face maximum. On the path P_4 at N = 150 and 300 the
full dynamic program is too large for the default run, so there method B is
checked against the discrete torus integral of verify_second_order.py instead.

Run with python -B verify_examples.py, or add --full for C_5 at N = 72, the path
P_4 at N = 150 and 300, and the census of all connected graphs on 6 states.
"""
import argparse
import itertools
import math
import sys
import time
from fractions import Fraction
from math import ceil, comb, cos, floor, log, pi, sin, sqrt

import mpmath as mp
import numpy as np
import sympy as sp
from scipy.optimize import brentq, minimize

from verify_second_order import RunFace, S_ab, torus_logP

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
    return 0.5 * 10.0 ** (exp10 - dec) * (1 + 1e-9) + 1e-15


def agree(label, printed, values, extra=''):
    target = float(printed)
    t = tol_of(printed)
    ok = all(abs(float(v) - target) <= t for v in values.values())
    shown = ', '.join(f'{k} {float(v):.10g}' for k, v in values.items())
    check(label, ok, f'paper {printed}; {shown}{extra}')


# ---------------------------------------------------------------- graphs (symmetric rate matrices W)

def W_cycle(d):
    W = np.zeros((d, d))
    for i in range(d):
        W[i, (i + 1) % d] = W[(i + 1) % d, i] = 1
    return W


def W_path(d):
    W = np.zeros((d, d))
    for i in range(d - 1):
        W[i, i + 1] = W[i + 1, i] = 1
    return W


def W_complete(d):
    return np.ones((d, d)) - np.eye(d)


def W_house():
    """square 1-2-3-4 (states 0..3) and roof 5 (state 4) joined to 1 and 2."""
    W = np.zeros((5, 5))
    for a, b in [(0, 1), (1, 2), (2, 3), (3, 0), (4, 0), (4, 1)]:
        W[a, b] = W[b, a] = 1
    return W


def W_paw():
    """The paper's states 4 (leaf), 1 (hub), 2, 3 are the indices 0, 1, 2, 3."""
    W = np.zeros((4, 4))
    for a, b in [(0, 1), (1, 2), (1, 3), (2, 3)]:
        W[a, b] = W[b, a] = 1
    return W


def W_triangles(eps):
    """triangles A = {1,2,3} and B = {4,5,6} (states 0..5), link 3-4 of rate eps."""
    W = np.zeros((6, 6))
    for a, b in [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)]:
        W[a, b] = W[b, a] = 1
    W[2, 3] = W[3, 2] = eps
    return W


def gen(W):
    Q = np.array(W, float)
    np.fill_diagonal(Q, 0)
    np.fill_diagonal(Q, -Q.sum(1))
    return Q


def connected(W, F):
    F = list(F)
    seen = {F[0]}
    stack = [F[0]]
    while stack:
        i = stack.pop()
        for j in F:
            if j not in seen and W[i][j] != 0:
                seen.add(j)
                stack.append(j)
    return len(seen) == len(F)


def exit_rates(W, method='A'):
    """lambda_F for every connected face (dict: tuple F -> value)."""
    Q = gen(W)
    d = len(W)
    out = {}
    for s in range(1, d + 1):
        for F in itertools.combinations(range(d), s):
            if not connected(W, F):
                continue
            M = -Q[np.ix_(F, F)]
            if method == 'A':
                out[F] = float(np.linalg.eigvalsh(M).min())
            else:
                with mp.workdps(40):
                    ev = mp.eigsy(mp.matrix(M.tolist()), eigvals_only=True) if s > 1 else [mp.mpf(M[0, 0])]
                    out[F] = float(min(ev))
    return out


def winners_hull(lams, d):
    """Method A: lower-left hull of (s-1, mu_s). Returns [(tau_enter, size)]."""
    mu = {}
    for F, l in lams.items():
        s = len(F)
        mu[s] = min(mu.get(s, np.inf), l)
    sizes = sorted(mu)
    pts = [(s - 1, mu[s]) for s in sizes]
    # lower convex hull, from the smallest size, keeping only decreasing mu
    hull = []
    for p in pts:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            if (x2 - x1) * (p[1] - y1) - (y2 - y1) * (p[0] - x1) <= 1e-13:
                hull.pop()
            else:
                break
        hull.append(p)
    # keep the part with decreasing mu (exposed by directions (tau, 1), tau > 0)
    out = [(0.0, hull[0][0] + 1)]
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        if y2 < y1 - 1e-13:
            out.append(((x2 - x1) / (y1 - y2), x2 + 1))
    return out, mu


def winners_scan(lams, taus):
    """Method B: argmin over all faces of tau lambda + |F| - 1 on a grid, then exact switch values."""
    faces = list(lams)
    lam = np.array([lams[F] for F in faces])
    siz = np.array([len(F) for F in faces])
    best = []
    for t in taus:
        c = t * lam + siz - 1
        m = c.min()
        best.append(min(len(F) for F, v in zip(faces, c) if v <= m + 1e-12))
    out = [(0.0, best[0])]
    for a, b, t0 in zip(best, best[1:], taus):
        if a != b:
            la = min(lams[F] for F in faces if len(F) == a)
            lb = min(lams[F] for F in faces if len(F) == b)
            out.append(((b - a) / (la - lb), b))
    return out


def same_winners(w1, w2):
    return len(w1) == len(w2) and all(a[1] == b[1] and abs(a[0] - b[0]) < 1e-9 for a, b in zip(w1, w2))


# ---------------------------------------------------------------- exact law, method A (packed dynamic program)

def binom_table(nmax, rmax):
    B = np.zeros((nmax + 1, rmax + 1), dtype=np.int64)
    for n in range(nmax + 1):
        for r in range(rmax + 1):
            B[n, r] = comb(n, r)
    return B


def ranks(comps, Bt):
    d = comps.shape[1]
    S = np.cumsum(comps[:, :d - 1], axis=1) + np.arange(d - 1)
    r = np.zeros(len(comps), dtype=np.int64)
    for i in range(d - 1):
        r += Bt[S[:, i], i + 1]
    return r


def full_law(Q, N, Ts, start=None):
    """Exact law of the composition for a batch of T values: (probs[rank, T], comps[rank])."""
    Q = np.asarray(Q, dtype=float)
    d = Q.shape[0]
    Ts = np.atleast_1d(np.asarray(Ts, dtype=float))
    nT = len(Ts)
    P = np.eye(d)[None, :, :] + (Ts / N)[:, None, None] * Q[None, :, :]
    Bt = binom_table(N + d, d)
    if start is None:
        start = np.full(d, 1.0 / d)
    comps = np.eye(d, dtype=np.int32)
    order = np.argsort(ranks(comps, Bt))
    comps = comps[order]
    A = np.zeros((nT, d, d))
    for idx in range(d):
        j = int(np.argmax(comps[idx]))
        A[:, idx, j] = start[j]
    for k in range(2, N + 1):
        Mk = comb(k + d - 1, d - 1)
        S = np.cumsum(comps[:, :d - 1], axis=1) + np.arange(d - 1)
        V = np.matmul(A, P)
        B = np.zeros((nT, Mk, d))
        newcomps = np.zeros((Mk, d), dtype=np.int32)
        for j in range(d):
            r = np.zeros(len(comps), dtype=np.int64)
            for i in range(d - 1):
                r += Bt[S[:, i] + (1 if i >= j else 0), i + 1]
            B[:, r, j] = V[:, :, j]
            newcomps[r] = comps
            newcomps[r, j] += 1
        A = B
        comps = newcomps
    return A.sum(axis=2).T, comps


def mode_supports(Q, N, Ts):
    """Support (as a sorted tuple) of the global mode at each T, by the full dynamic program."""
    probs, comps = full_law(Q, N, Ts)
    out = []
    for t in range(len(Ts)):
        c = comps[int(np.argmax(probs[:, t]))]
        out.append(tuple(i for i in range(len(c)) if c[i] > 0))
    return out


# ---------------------------------------------------------------- face maxima, method B

class FaceMax:
    """Maximum of P_N(n) over compositions with support exactly F (run expansion and a lattice search)."""

    def __init__(self, W, F, mu_full, mmax):
        Q = gen(W)
        F = list(F)
        A = Q[np.ix_(F, F)].copy()
        np.fill_diagonal(A, 0)
        self.q = -np.diag(Q)[F]
        self.A = A
        self.mu = np.asarray(mu_full, float)[F]
        self.k = len(F)
        self.rf = RunFace(A, self.q, self.mu, mmax) if self.k > 1 else None
        self.x0 = None

    def lp(self, n, h, method='A'):
        if method == 'A':
            return self.rf.logP(n, h)
        return torus_logP(self.A, self.q, self.mu, n, h)

    def value(self, N, T, method='A', radius=2, center=None):
        h = T / N
        if self.k == 1:
            return log(self.mu[0]) + (N - 1) * math.log1p(-h * self.q[0]), (N,)
        if self.k == 2:
            ns = np.arange(1, N)
            vals = [self.lp([a, N - a], h, method) for a in ns]
            j = int(np.argmax(vals))
            return vals[j], (int(ns[j]), N - int(ns[j]))
        k = self.k
        if center is None:
            x0 = np.full(k - 1, 1.0 / k) if self.x0 is None else self.x0
            f = lambda x: -self.lp(N * np.concatenate([[1 - x.sum()], x]), h, method) if (x.min() > 0 and x.sum() < 1) else 1e300
            r = minimize(f, x0, method='Nelder-Mead', options=dict(xatol=1e-9, fatol=1e-13, maxiter=6000))
            self.x0 = r.x
            c = np.round(N * r.x).astype(int)
        else:                                    # the real maximum is known by symmetry
            c = np.round(N * np.asarray(center[1:])).astype(int)
        best = (-np.inf, None)
        for off in itertools.product(range(-radius, radius + 1), repeat=k - 1):
            tail = c + np.array(off)
            first = N - tail.sum()
            if first < 1 or tail.min() < 1:
                continue
            v = self.lp([first] + list(tail), h, method)
            if v > best[0]:
                best = (v, tuple([int(first)] + [int(x) for x in tail]))
        return best


def global_mode(facemaxes, N, T, method='A'):
    vals = {name: fm.value(N, T, method) for name, fm in facemaxes.items()}
    name = max(vals, key=lambda n: vals[n][0])
    return name, vals


# ======================================================================== checks

def check_complete_and_census(full):
    print('\nTable 1, rows K_d and symmetric Q: complete graphs, single jumps, and a census of small graphs', flush=True)
    worst = 0.0
    for d in range(2, 7):
        l = exit_rates(W_complete(d))
        worst = max(worst, max(abs(v - (d - len(F))) for F, v in l.items()))
    check('(a) lambda_F = d - |F| on K_d, d = 2..6', worst < 1e-12, f'max error {worst:.1e}')
    rng = np.random.default_rng(5)
    bad = 0
    eq_ok = True
    for trial in range(300):
        d = rng.integers(3, 7)
        W = rng.uniform(0, 2, (d, d)) * (rng.uniform(size=(d, d)) < 0.7)
        W = np.triu(W, 1) + np.triu(W, 1).T
        Q = gen(W)
        for x in range(d):
            qx = -Q[x, x]
            rest = [i for i in range(d) if i != x]
            lam = float(np.linalg.eigvalsh(-Q[np.ix_(rest, rest)]).min())
            if lam > qx / (d - 1) + 1e-12:
                bad += 1
    for d in range(3, 7):
        W = rng.uniform(0.5, 2, (d, d))
        W = np.triu(W, 1) + np.triu(W, 1).T
        W[0, 1:] = W[1:, 0] = 0.7                  # state 0 joined to all at a common rate
        Q = gen(W)
        lam = float(np.linalg.eigvalsh(-Q[1:, 1:]).min())
        eq_ok &= abs(lam - (-Q[0, 0]) / (d - 1)) < 1e-12
    check('(b) lambda_{[d]-x} <= q_x/(d-1), with equality for a common rate', bad == 0 and eq_ok,
          f'{bad} violations in 300 random symmetric generators; equality cases {"hold" if eq_ok else "fail"}')
    # (d) census: for unit rates the winners are vertices then [d] iff the graph is complete
    dmax = 6 if full else 5
    counts = {}
    for d in range(3, dmax + 1):
        pairs = list(itertools.combinations(range(d), 2))
        n_conn = n_bad = 0
        for mask in range(1 << len(pairs)):
            W = np.zeros((d, d))
            for b, (i, j) in enumerate(pairs):
                if mask >> b & 1:
                    W[i, j] = W[j, i] = 1
            if not connected(W, range(d)):
                continue
            n_conn += 1
            lams = exit_rates(W)
            w, mu = winners_hull(lams, d)
            single = [s for _, s in w] == [1, d]
            complete = mask == (1 << len(pairs)) - 1
            if single != complete:
                n_bad += 1
        counts[d] = (n_conn, n_bad)
    check('(d) unit rates: single jump iff complete (all connected labelled graphs)', all(b == 0 for _, b in counts.values()),
          ', '.join(f'd = {d}: {c} graphs, {b} exceptions' for d, (c, b) in counts.items()))


def check_cycles():
    print('\nTable 1, row C_d: arcs and the cycle cascade', flush=True)
    lam = lambda k: 4 * sin(pi / (2 * (k + 1))) ** 2        # = 2 - 2cos(pi/(k+1)), without cancellation
    # arcs, and non-arc faces (Remark 5.3)
    worst = 0.0
    for d in range(3, 11):
        lA = exit_rates(W_cycle(d))
        for F, v in lA.items():
            if len(F) < d:
                worst = max(worst, abs(v - lam(len(F))))
    check('lambda of an arc of k states = 2 - 2cos(pi/(k+1)) (all connected faces of C_d, d = 3..10)', worst < 1e-12, f'max error {worst:.1e}')
    D = lambda k: k + lam(k) / (lam(k - 1) - lam(k))
    ok = abs(D(2) - 3) < 1e-12 and all(1.5 * k - 0.5 < D(k) < 1.5 * k for k in range(3, 2001))
    check('D_2 = 3 and 3k/2 - 1/2 < D_k < 3k/2 for 3 <= k <= 2000', ok, f'D_3 = {D(3):.6f}, D_10 = {D(10):.6f}')
    m = 4
    lhs = pi ** 2 / 12 * (2 * m - 1) / (m - 1) ** 2 + pi ** 4 / (960 * m * m)
    rhs = 1 - pi ** 2 / (24 * (m - 1) ** 2)
    agree('sinc inequality at m = 4, left side', '0.6460', {'value': lhs})
    agree('sinc inequality at m = 4, right side', '0.9543', {'value': rhs})
    mono = all(pi ** 2 / 12 * (2 * a - 1) / (a - 1) ** 2 + pi ** 4 / (960 * a * a) > pi ** 2 / 12 * (2 * a + 1) / a ** 2 + pi ** 4 / (960 * (a + 1) ** 2)
               for a in range(4, 500))
    check('left side decreases and right side increases in m', mono, 'm = 4..500')
    # Table 1, row C_d: winners on C_d from the hull (A) and from a direct scan (B)
    taus = np.linspace(0.01, 80, 40000)
    least = {}
    all_ok = True
    for d in range(3, 13):
        lams = exit_rates(W_cycle(d))
        wA, mu = winners_hull(lams, d)
        wB = winners_scan(lams, taus) if d <= 10 else wA
        K = floor(2 * d / 3)
        if d == 3:
            pred = [(0.0, 1), (1.0, 3)]
        else:
            pred = [(0.0, 1)] + [(1 / (lam(k - 1) - lam(k)), k) for k in range(2, K + 1)] + [(ceil(d / 3) / lam(K), d)]
        ok = same_winners(wA, pred) and same_winners(wB, pred)
        all_ok &= ok
        for _, s in wA:
            if s < d:
                least.setdefault(s, d)
    check('Table 1, row C_d: winners and switch values on C_d, d = 3..12 (hull and direct scan)', all_ok, 'arcs of 1..floor(2d/3) states, then C_d')
    agree('tau_4 = 2/(1 - 2 sqrt2 + sqrt5)', '4.906280', {'closed': 2 / (1 - 2 * sqrt(2) + sqrt(5)), 'eigen': 1 / (lam(3) - lam(4))})
    agree('tau_5 = 1/(sqrt3 - (1+sqrt5)/2)', '8.770636', {'closed': 1 / (sqrt(3) - (1 + sqrt(5)) / 2), 'eigen': 1 / (lam(4) - lam(5))})
    agree('tau_3 = 1 + sqrt2', '2.414214', {'closed': 1 + sqrt(2), 'eigen': 1 / (lam(2) - lam(3))})
    want = {2: 4, 3: 5, 4: 6, 5: 8, 6: 9, 7: 11, 8: 12}
    check('least d with arc k winning (Table 1): 4, 5, 6, 8, 9, 11, 12', all(least.get(k) == v for k, v in want.items()) and
          all(ceil(3 * k / 2) == v for k, v in want.items() if k >= 3), f'from the hulls: {dict((k, least.get(k)) for k in want)}')
    for d, closed, label in [(4, 2.0, '2'), (5, 2 + sqrt(2), '2 + sqrt2'), (6, 3 + sqrt(5), '3 + sqrt5'), (8, 6 + 3 * sqrt(3), '6 + 3 sqrt3')]:
        K = floor(2 * d / 3)
        wA, _ = winners_hull(exit_rates(W_cycle(d)), d)
        check(f'tau_full(C_{d}) = {label}', abs(wA[-1][0] - closed) < 1e-9 and abs(ceil(d / 3) / lam(K) - closed) < 1e-12,
              f'hull {wA[-1][0]:.9f}, formula {ceil(d / 3) / lam(K):.9f}')
    wA, _ = winners_hull(exit_rates(W_cycle(6)), 6)
    agree('Figure 2(a): C_6 switch at 4.906', '4.906', {'hull': wA[3][0]})
    ks = np.array([100, 200, 400, 800])
    tk = 1 / (np.array([lam(k - 1) for k in ks]) - np.array([lam(k) for k in ks]))
    resid = (tk - ks ** 3 / (2 * pi ** 2) - 3 * ks ** 2 / (4 * pi ** 2)) / ks
    check('(d) tau_k = k^3/(2 pi^2) + 3k^2/(4 pi^2) + O(k)', np.ptp(resid) < 0.01, f'(tau_k - two terms)/k = {np.round(resid, 4)}')
    ds = np.array([300, 3000, 30000])
    tf = np.array([ceil(d / 3) / lam(floor(2 * d / 3)) for d in ds]) / (4 * ds ** 3 / (27 * pi ** 2))
    check('(d) tau_full(d) ~ 4d^3/(27 pi^2)', abs(tf[-1] - 1) < 1e-3 and abs(tf[-1] - 1) < abs(tf[0] - 1), f'ratios {np.round(tf, 5)}')
    # heights of the nearest non-winning point above the hull
    heights = {}
    for name, W in [('C_4', W_cycle(4)), ('C_5', W_cycle(5)), ('C_6', W_cycle(6)), ('house', W_house()), ('paw', W_paw())]:
        lams = exit_rates(W)
        d = len(W)
        w, mu = winners_hull(lams, d)
        win = [s for _, s in w]
        hs = []
        for s in range(1, d + 1):
            if s in win:
                continue
            lo = max(x for x in win if x < s)
            hi = min(x for x in win if x > s)
            chord = mu[lo] + (mu[hi] - mu[lo]) * (s - lo) / (hi - lo)
            hs.append(mu[s] - chord)
        heights[name] = min(hs) if hs else np.inf       # on the paw every size wins
    agree('height of the nearest non-winning point on C_6 (least of the graphs)', '0.077', {'C_6': heights['C_6']})
    check('C_4, C_5, the house and the paw have larger heights (the paw has no non-winning size)', min(heights.values()) == heights['C_6'],
          ', '.join(f'{k} {v:.4f}' for k, v in heights.items()))


def check_paths(full):
    print('\nTable 1, rows P_d and P_4: paths', flush=True)
    lp = lambda k: 4 * sin(pi / (2 * (2 * k + 1))) ** 2     # = 2 - 2cos(pi/(2k+1))
    worst = 0.0
    for d in range(3, 10):
        lams = exit_rates(W_path(d))
        for k in range(1, d):
            worst = max(worst, abs(lams[tuple(range(k))] - lp(k)))
        wA, mu = winners_hull(lams, d)
        K = floor(2 * d / 3)
        worst = max(worst, 0 if [s for _, s in wA] == list(range(1, K + 1)) + [d] else 1)
    check('end-arc exit rate 2 - 2cos(pi/(2k+1)) and winners 1..floor(2d/3), then P_d (d = 3..9)', worst < 1e-12, f'max error {worst:.1e}')
    agree('first switch at the golden ratio', '1.618034', {'closed': (1 + sqrt(5)) / 2, 'eigen': 1 / (lp(1) - lp(2))})
    Dp = lambda k: k + lp(k) / (lp(k - 1) - lp(k))
    agree("D'_3 on P_4", '4.077', {'value': Dp(3)})
    with mp.workdps(50):                         # the lower margin is small, so use 50 digits here
        lpm = lambda k: 4 * mp.sin(mp.pi / (2 * (2 * k + 1))) ** 2
        Dpm = lambda k: k + lpm(k) / (lpm(k - 1) - lpm(k))
        ok = all(mp.mpf(3) * k / 2 - mp.mpf(1) / 2 < Dpm(k) < mp.mpf(3) * k / 2 for k in range(2, 2001))
        gap = min(Dpm(k) - (mp.mpf(3) * k / 2 - mp.mpf(1) / 2) for k in (10, 100, 1000, 2000))
    check("3k/2 - 1/2 < D'_k < 3k/2 for 2 <= k <= 2000", ok, f'least lower margin at k = 10, 100, 1000, 2000: {mp.nstr(gap, 3)}')
    check('1 - pi^2/216 > 0.954', 1 - pi ** 2 / 216 > 0.954, f'{1 - pi ** 2 / 216:.6f}')
    agree('left side of the path inequality at k = 2', '0.414', {'value': pi ** 2 / 24 + pi ** 4 / (7680 * 4)})
    agree('right side of the path inequality at k = 2', '1.113', {'value': 0.318 * 14 / 4})
    check('(2k-1)^2 (k+1) - (k-1)(2k+1)^2 = 2', all((2 * k - 1) ** 2 * (k + 1) - (k - 1) * (2 * k + 1) ** 2 == 2 for k in range(1, 100)), 'k = 1..99')
    agree('height of the end-arc of 3 states above the hull on P_4', '0.0071', {'value': lp(3) - lp(2) / 2})
    # exact windows of the end-arc of 3 states on P_4
    W = W_path(4)
    Q = gen(W)
    mu = np.ones(4) / 4
    faces = {'end vertex': (0,), 'middle vertex': (1,), 'end edge': (0, 1), 'middle edge': (1, 2), 'end-arc 3': (0, 1, 2), 'P_4': (0, 1, 2, 3)}
    printed = {40: ('9.381', '12.502'), 72: ('12.176', '15.142'), 150: ('15.804', '18.443'), 300: ('19.292', '21.590')}
    ratios = {}
    for N in ((40, 72, 150, 300) if full else (40, 72)):
        fm = {n: FaceMax(W, F, mu, mmax={1: 1, 2: N, 3: min(N, 120), 4: min(N, 40)}[len(F)]) for n, F in faces.items()}
        dA = lambda T, a, b: fm[a].value(N, T)[0] - fm[b].value(N, T)[0]
        Tin = brentq(lambda T: dA(T, 'end-arc 3', 'end edge'), 0.8 * float(printed[N][0]), 1.1 * float(printed[N][0]), xtol=1e-7)
        Tout = brentq(lambda T: dA(T, 'P_4', 'end-arc 3'), 0.9 * float(printed[N][1]), 1.1 * float(printed[N][1]), xtol=1e-7)
        # the mode is the end-arc inside the window and not just outside it (method B, all faces)
        inside = global_mode(fm, N, 0.5 * (Tin + Tout))[0]
        before = global_mode(fm, N, Tin - 0.01)[0]
        after = global_mode(fm, N, Tout + 0.01)[0]
        if N <= 72 or (full and N <= 150):
            sup = mode_supports(Q, N, [Tin - 1e-5, Tin + 1e-5, Tout - 1e-5, Tout + 1e-5])
            # the path has a mirror symmetry, so either end may carry the mode
            okA = sup[0] in [(0, 1), (2, 3)] and sup[1] in [(0, 1, 2), (1, 2, 3)] and sup[2] in [(0, 1, 2), (1, 2, 3)] and sup[3] == (0, 1, 2, 3)
            check(f'N = {N}: the full dynamic program flips at both ends', okA, f'supports at T -+ 1e-5: {sup}')
        else:
            # the discrete torus integral recomputes the 2 face maxima at the crossings
            gin = fm['end-arc 3'].value(N, Tin, 'B')[0] - fm['end edge'].value(N, Tin, 'B')[0]
            gout = fm['P_4'].value(N, Tout, 'B')[0] - fm['end-arc 3'].value(N, Tout, 'B')[0]
            check(f'N = {N}: the torus integral puts both crossings at the same T', abs(gin) < 1e-7 and abs(gout) < 1e-7,
                  f'differences of log face maxima {gin:+.1e}, {gout:+.1e}')
        check(f'N = {N}: order end edge -> end-arc 3 -> P_4 around the window', (before, inside, after) == ('end edge', 'end-arc 3', 'P_4'),
              f'modes {before}, {inside}, {after}')
        agree(f'N = {N}: window starts', printed[N][0], {'B': Tin})
        agree(f'N = {N}: window ends', printed[N][1], {'B': Tout})
        ratios[N] = Tout / Tin
    agree('window ratio at N = 40', '1.333', {'B': ratios[40]})
    if full:
        agree('window ratio at N = 300', '1.119', {'B': ratios[300]})


def check_dp_exact():
    print('\nThe dynamic program of the whole chain against all d^N words in exact arithmetic', flush=True)
    worst = 0.0
    cells = [('C_4', W_cycle(4), 8), ('K_4', W_complete(4), 8), ('C_5', W_cycle(5), 7), ('paw', W_paw(), 8),
             ('two triangles, eps = 1', W_triangles(1.0), 6), ('two triangles, eps = 1/2', W_triangles(0.5), 6)]
    for name, W, N in cells:
        d = len(W)
        T = Fraction(3)
        h = T / N
        Wf = [[Fraction(W[i][j]).limit_denominator(1000) for j in range(d)] for i in range(d)]
        P = [[(1 - h * sum(Wf[i][l] for l in range(d) if l != i)) if i == j else h * Wf[i][j] for j in range(d)] for i in range(d)]
        exact = {}
        for w in itertools.product(range(d), repeat=N):
            pr = Fraction(1, d)
            for a, b in zip(w, w[1:]):
                pr *= P[a][b]
                if pr == 0:
                    break
            if pr:
                c = tuple(w.count(i) for i in range(d))
                exact[c] = exact.get(c, 0) + pr
        probs, comps = full_law(gen(W), N, [3.0])
        for p, c in zip(probs[:, 0], comps):
            e = exact.get(tuple(int(x) for x in c), 0)
            if e:
                worst = max(worst, abs(p / float(e) - 1))
            else:
                worst = max(worst, abs(p))
    check('packed dynamic program = exact enumeration (paper: 1e-15)', worst < 1e-14,
          f'max relative difference {worst:.1e} on C_4, K_4 (N = 8), C_5 (N = 7), the paw (N = 8) and 2 triangles (N = 6)')


def check_C5(full):
    print('\nFigure 2(b): the exact mode on C_5', flush=True)
    W = W_cycle(5)
    Q = gen(W)
    mu = np.ones(5) / 5
    faces = {'arc1': (0,), 'arc2': (0, 1), 'arc3': (0, 1, 2), 'full': (0, 1, 2, 3, 4)}
    # The ledger lists the left ends of bisection brackets, 6.883528 at N = 40 and 6.389394 at N = 72.
    # Rounded to 6 decimals these 2 transitions are 6.883529 and 6.389395, and the full dynamic program
    # below confirms each transition to within 2e-7.
    printed = {40: ('2.538112', '5.122981', '6.883529'), 72: ('3.077562', '6.389395', '8.601750')}
    for N in ((40, 72) if full else (40,)):
        fm = {n: FaceMax(W, F, mu, mmax=N if len(F) < 5 else N // 5 + 3) for n, F in faces.items()}
        # the balanced pair is exact by Proposition 4.9 and Paper A
        u_of = lambda T: (T / N) / (1 - 2 * T / N)
        t1 = brentq(lambda T: S_ab(N // 2, N // 2, u_of(T)) - 1, 0.5, 6, xtol=1e-12)
        t1b = brentq(lambda T: fm['arc2'].value(N, T)[0] - fm['arc1'].value(N, T)[0], 0.5, 6, xtol=1e-10)
        t2 = brentq(lambda T: fm['arc3'].value(N, T)[0] - fm['arc2'].value(N, T)[0], t1 + 0.5, 3 * t1, xtol=1e-10)
        # by the rotation symmetry the real maximum on C_5 is the uniform point
        t3 = brentq(lambda T: fm['full'].value(N, T, radius=2, center=np.full(5, 0.2))[0] - fm['arc3'].value(N, T)[0],
                    t2 + 0.2, 2 * t2, xtol=1e-10)
        d = 2e-7
        Ts = [t1 - d, t1 + d, t2 - d, t2 + d, t3 - d, t3 + d]
        sup = sum((mode_supports(Q, N, Ts[i:i + 2]) for i in range(0, 6, 2)), [])
        sizes = [len(s) for s in sup]
        check(f'N = {N}: the full dynamic program flips 1 -> 2 -> 3 -> 5 states within 2e-7 of these T', sizes == [1, 2, 2, 3, 3, 5],
              f'support sizes at T -+ 2e-7: {sizes}')
        agree(f'N = {N}: vertex -> 2-arc', printed[N][0], {'Paper A root': t1, 'face maxima': t1b})
        agree(f'N = {N}: 2-arc -> 3-arc', printed[N][1], {'face maxima': t2})
        agree(f'N = {N}: 3-arc -> C_5', printed[N][2], {'face maxima': t3})
        if N == 40:
            L = log(N)
            b3 = -0.9379218441
            agree('N = 40: tau_3 (L - (1/2) log L + b_3)', '5.07', {'value': (1 + sqrt(2)) * (L - 0.5 * log(L) + b3)})
            agree('N = 40: exact switch from 2 to 3 states', '5.12', {'face maxima': t2})
            agree('N = 40: tau_3 log N', '8.91', {'value': (1 + sqrt(2)) * L})


def check_triangles():
    print('\nTable 1, row Theta_eps: two triangles joined by a weak link', flush=True)
    e = sp.symbols('epsilon', positive=True)
    x = sp.symbols('x')
    pA = x ** 2 - (3 + e) * x + e
    p4 = x ** 3 - (5 + 2 * e) * x ** 2 + (6 + 6 * e) * x - 2 * e
    p5 = x ** 3 - (4 + 2 * e) * x ** 2 + (3 + 4 * e) * x - e
    # characteristic polynomials from the matrices themselves
    M = sp.zeros(6, 6)
    for a, b in [(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5)]:
        M[a, b] = M[b, a] = -1
    M[2, 3] = M[3, 2] = -e
    for i in range(6):
        M[i, i] = -sum(M[i, j] for j in range(6) if j != i)
    cp = lambda F: sp.factor(sp.expand((M.extract(F, F) - x * sp.eye(len(F))).det()))
    ok = (sp.expand(cp([0, 1, 2]) + (x - 3) * pA) == 0 and sp.expand(cp([0, 1, 2, 3]) - (x - 3) * p4) == 0
          and sp.expand(cp([1, 2, 3, 4, 5]) + (x - 3) ** 2 * p5) == 0)
    check('det(xI + Q_F) = (x-3) p_A, (x-3) p_4 and (x-3)^2 p_5', ok, 'sympy, up to the sign (-1)^|F|')
    r1 = sp.factor(sp.resultant(p5, p4.subs(x, 2 * x), x))
    r2 = sp.factor(sp.resultant(pA.subs(x, sp.Rational(3, 2) * x), p4, x))
    r3 = sp.factor(sp.resultant(pA.subs(x, (1 + x) / 2), p4, x))
    check('Res(p_5(x), p_4(2x)) = -8 eps^3 (16 eps^2 + 12 eps + 9)', sp.expand(r1 + 8 * e ** 3 * (16 * e ** 2 + 12 * e + 9)) == 0, str(r1))
    check('Res(p_A(3x/2), p_4(x)) = -eps^2 (120 eps^2 - 256 eps + 135)/16', sp.expand(r2 + e ** 2 * (120 * e ** 2 - 256 * e + 135) / 16) == 0, str(r2))
    check('Res(p_A((1+x)/2), p_4(x)) = (eps^3 + 2 eps^2 - 19 eps - 45)/8', sp.expand(r3 - (e ** 3 + 2 * e ** 2 - 19 * e - 45) / 8) == 0, str(r3))
    eps1 = (64 + sqrt(46)) / 60
    eps0 = (64 - sqrt(46)) / 60
    roots = [complex(z) for z in np.roots([1, 2, -19, -45])]
    eps2 = max(z.real for z in roots if abs(z.imag) < 1e-12)
    agree('eps_1 = (64 + sqrt46)/60', '1.17971', {'closed': eps1, 'root of 120e^2 - 256e + 135': max(np.roots([120, -256, 135]).real)})
    agree('eps_0 = (64 - sqrt46)/60', '0.95363', {'closed': eps0})
    agree('eps_2', '4.48108', {'numpy root': eps2, 'bisection': brentq(lambda t: t ** 3 + 2 * t * t - 19 * t - 45, 4, 5, xtol=1e-12)})
    # the certificate at eps_0 (exact rational arithmetic)
    E = sp.Symbol('E')
    p4x0 = sp.expand(p4.subs({x: sp.Rational(7, 40), e: E}))
    pAx0 = sp.expand(pA.subs({x: sp.Rational(21, 80), e: E}))
    check('p_4(7/40) = 57743/64000 - 809 eps/800 and p_A(21/80) = 59 eps/80 - 4599/6400',
          sp.expand(p4x0 - (sp.Rational(57743, 64000) - sp.Rational(809, 800) * E)) == 0 and sp.expand(pAx0 - (sp.Rational(59, 80) * E - sp.Rational(4599, 6400))) == 0, '')
    lo = 57743 / 64000 * 800 / 809
    hi = 4599 / 6400 * 80 / 59
    check('both are negative on (0.8923, 0.9743), which contains eps_0', lo <= 0.8923 and 0.9743 <= hi and 0.8923 < eps0 < 0.9743,
          f'exact interval ({lo:.6f}, {hi:.6f})')
    # numbers: the winners from all 63 faces against the closed forms, for several eps
    lamA = lambda t: (3 + t - sqrt(t * t + 2 * t + 9)) / 2
    least = lambda coeffs: min(r.real for r in np.roots(coeffs) if abs(r.imag) < 1e-9)
    all_ok = True
    detail = []
    for t in (0.3, 1.0, 1.1, 1.5, 3.0, 4.4, 4.6, 8.0):
        lams = exit_rates(W_triangles(t))
        lamsB = exit_rates(W_triangles(t), 'B')
        wA, mu = winners_hull(lams, 6)
        wA2, _ = winners_hull(lamsB, 6)
        m4 = least([1, -(5 + 2 * t), 6 + 6 * t, -2 * t])
        m5 = least([1, -(4 + 2 * t), 3 + 4 * t, -t])
        closed_mu = {1: 2.0, 2: 1.0, 3: lamA(t), 4: m4, 5: m5, 6: 0.0}
        okmu = all(abs(mu[s] - closed_mu[s]) < 1e-10 for s in closed_mu)
        la = lamA(t)
        if t < eps1:
            pred = [(0.0, 1), (1.0, 2), (1 / (1 - la), 3), (3 / la, 6)]
        elif t < eps2:
            pred = [(0.0, 1), (1.0, 2), (1 / (1 - la), 3), (1 / (la - m4), 4), (2 / m4, 6)]
        else:
            pred = [(0.0, 1), (1.0, 2), (2 / (1 - m4), 4), (2 / m4, 6)]
        ok = okmu and same_winners(wA, pred) and same_winners(wA2, pred) and abs(1 / (1 - la) - (1 + t + sqrt(t * t + 2 * t + 9)) / 4) < 1e-12 \
            and abs(3 / la - 1.5 / t * (3 + t + sqrt(t * t + 2 * t + 9))) < 1e-9
        all_ok &= ok
        detail.append(f'{t}: sizes {[s for _, s in wA]}')
    check('(b), (c): the least exit rates by size and the winner phases from all 63 faces (numpy and mpmath) match the closed forms', all_ok, '; '.join(detail))
    t = 1e-3
    check('(a), (c): lambda_A = eps/3 - 2 eps^2/27 + O(eps^3) and tau* = 9/eps + 2 + 2eps/9 + O(eps^2)',
          abs(lamA(t) - (t / 3 - 2 * t * t / 27)) < 5 * t ** 3 and abs(3 / lamA(t) - (9 / t + 2 + 2 * t / 9)) < 5 * t * t, f'at eps = {t}')
    ok = all(least([1, -(5 + 2 * t), 6 + 6 * t, -2 * t]) <= (3 - sqrt(5)) / 2 + 1e-12 for t in np.geomspace(1e-3, 1e4, 200))
    check('least exit rate of size 4 <= (3 - sqrt5)/2 for every eps', ok, '200 values of eps from 1e-3 to 1e4')


def check_paw_house():
    print('\nTable 1, rows paw, house and K_4 plus a vertex', flush=True)
    lA = exit_rates(W_paw())
    lB = exit_rates(W_paw(), 'B')
    closed = {(0,): 1, (2,): 2, (3,): 2, (1,): 3, (0, 1): 2 - sqrt(2), (2, 3): 1, (1, 2): (5 - sqrt(5)) / 2, (1, 3): (5 - sqrt(5)) / 2,
              (1, 2, 3): 2 - sqrt(3), (0, 1, 2): 2 - 2 * cos(2 * pi / 9), (0, 1, 3): 2 - 2 * cos(2 * pi / 9), (0, 1, 2, 3): 0}
    worst = max(max(abs(lA[F] - v), abs(lB[F] - v)) for F, v in closed.items())
    check('paw: all 12 connected exit rates in closed form', worst < 1e-12 and set(lA) == set(closed), f'max error {worst:.1e}')
    agree('paw: 2 - 2cos(2pi/9)', '0.468', {'closed': 2 - 2 * cos(2 * pi / 9), 'root of x^3 - 6x^2 + 9x - 3': min(np.roots([1, -6, 9, -3]).real)})
    w, _ = winners_hull(lA, 4)
    pred = [(0.0, 1), (1 + sqrt(2), 2), (sqrt(2) + sqrt(3), 3), (2 + sqrt(3), 4)]
    check('paw (paper states: leaf 4 = index 0, 1 = index 1): winners {4}, {1,4} from 1+sqrt2, {1,2,3} from sqrt2+sqrt3, all from 2+sqrt3', same_winners(w, pred), str([(round(a, 6), s) for a, s in w]))
    lA = exit_rates(W_house())
    lB = exit_rates(W_house(), 'B')
    check('house: 31 faces, all connected ones computed twice', len([F for s in range(1, 6) for F in itertools.combinations(range(5), s)]) == 31
          and max(abs(lA[F] - lB[F]) for F in lA) < 1e-12, f'{len(lA)} connected faces')
    w, mu = winners_hull(lA, 5)
    pred = [(0.0, 1), (1.0, 2), (1 + sqrt(2), 3), (2 + sqrt(2), 5)]
    best2 = min(lA, key=lambda F: lA[F] if len(F) == 2 else 9)
    best3 = min(lA, key=lambda F: lA[F] if len(F) == 3 else 9)
    best1 = sorted(F for F in lA if len(F) == 1 and abs(lA[F] - 2) < 1e-12)
    check('house: winners {3},{4},{5}, then {3,4} from 1, {1,2,5} from 1+sqrt2, all from 2+sqrt2',
          same_winners(w, pred) and best2 == (2, 3) and best3 == (0, 1, 4) and best1 == [(2,), (3,), (4,)],
          f'{[(round(a, 6), s) for a, s in w]}; best pair {best2}, best triple {best3}')
    four = sorted(v for F, v in lA.items() if len(F) == 4)
    agree('house: margin between the 2 best faces of 4 states', '0.022', {'numpy': four[1] - four[0]})
    agree('house: lambda of V minus 3', '0.40385', {'numpy': lA[(0, 1, 3, 4)]})
    agree('house: lambda of V minus 1', '0.644', {'numpy': lA[(1, 2, 3, 4)]})


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--full', action='store_true', help='also run the larger cells')
    args = parser.parse_args()
    t0 = time.time()
    for step in (lambda: check_complete_and_census(args.full), check_dp_exact, check_cycles, lambda: check_paths(args.full),
                 lambda: check_C5(args.full), check_triangles, check_paw_house):
        t1 = time.time()
        step()
        print(f'  ({time.time() - t1:.0f} s)', flush=True)
    print(f'\nverify_examples: {len(FAILS)} failures, {time.time() - t0:.0f} s', flush=True)
    if FAILS:
        print('failed: ' + '; '.join(FAILS))
        sys.exit(1)


if __name__ == '__main__':
    main()
