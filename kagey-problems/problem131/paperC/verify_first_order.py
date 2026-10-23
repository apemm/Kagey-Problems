"""Checks for Sections 2 and 3 of Paper C (the exact law and first-order face selection).

Lemma 2.3 (the run expansion) is checked in exact rational arithmetic against 2
other exact computations: a list of all d^N words, and a forward dynamic program
of the chain. Lemma 2.4 is checked by integrating the continuum density over the
simplex and comparing with the probability, from matrix exponentials, that the
continuous-time chain stays in the face and visits all of its states.

The rate I_F of Proposition 3.1 is computed in 2 ways. Method A maximizes over u
as in its definition (Newton's method on a concave function). Method B is the
Legendre transform of the Perron root Lambda(theta) of Q_F + diag(theta),
maximized over theta. The minimizer of I_F is found by a direct numerical
minimization and compared with l_F o r_F.

For Theorem 3.4 the winners come from the lower convex hull of the points
(lambda_F, |F|-1) (method A) and from minimizing the cost over all admissible
faces on a fine grid of tau (method B). Lemma 2.2 is checked by listing the
supports of all words of positive probability.

Finally the face order at N = 64 on a star and a path with unequal rates is
found from face maxima computed with the run expansion (method B), and the
full dynamic program confirms each switch (method A).

Run with python -B verify_first_order.py, or add --full for the same cells at N = 160.
"""
import argparse
import itertools
import math
import sys
import time
from fractions import Fraction
from math import log

import numpy as np
from scipy.linalg import expm
from scipy.optimize import brentq, minimize

from verify_examples import full_law
from verify_second_order import RunFace

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


def gen(W):
    Q = np.array(W, dtype=object if isinstance(W[0][0], Fraction) else float)
    d = len(W)
    for i in range(d):
        Q[i][i] = 0
        Q[i][i] = -sum(Q[i][j] for j in range(d))
    return Q


def nr3():
    """The non-reversible cell NR3 of ledger_C1.md: a 3-cycle with drift, and a fourth state outside the face."""
    W = np.zeros((4, 4))
    W[0, 1] = W[1, 2] = W[2, 0] = 1.6
    W[1, 0] = W[2, 1] = W[0, 2] = 0.2
    W[0, 3], W[1, 3], W[2, 3] = 0.1, 0.5, 1.0
    W[3, 0] = W[3, 1] = W[3, 2] = 1.0
    return gen(W)


def star(r):
    W = np.zeros((4, 4))
    W[0, 1], W[1, 0], W[0, 2], W[2, 0], W[0, 3], W[3, 0] = r
    return gen(W)


def path(r):
    W = np.zeros((4, 4))
    W[0, 1], W[1, 0], W[1, 2], W[2, 1], W[2, 3], W[3, 2] = r
    return gen(W)


# ---------------------------------------------------------------- exact laws

def law_words(Q, mu, h, N):
    d = len(mu)
    P = [[(1 if i == j else 0) + h * Q[i][j] for j in range(d)] for i in range(d)]
    law = {}
    for w in itertools.product(range(d), repeat=N):
        p = mu[w[0]]
        for a, b in zip(w, w[1:]):
            p *= P[a][b]
            if p == 0:
                break
        if p:
            c = tuple(w.count(i) for i in range(d))
            law[c] = law.get(c, 0) + p
    return law


def law_dp(Q, mu, h, N):
    d = len(mu)
    P = [[(1 if i == j else 0) + h * Q[i][j] for j in range(d)] for i in range(d)]
    cur = {}
    for i in range(d):
        if mu[i]:
            c = [0] * d
            c[i] = 1
            cur[(tuple(c), i)] = mu[i]
    for _ in range(N - 1):
        nxt = {}
        for (c, i), p in cur.items():
            for j in range(d):
                if P[i][j]:
                    cc = list(c)
                    cc[j] += 1
                    nxt[(tuple(cc), j)] = nxt.get((tuple(cc), j), 0) + p * P[i][j]
        cur = nxt
    law = {}
    for (c, i), p in cur.items():
        law[c] = law.get(c, 0) + p
    return law


def law_runs(Q, mu, h, N):
    """Lemma 2.3: sum over run-count vectors m of W(m) h^(M-1) prod C(n_i-1, m_i-1)(1 - h q_i)^(n_i - m_i)."""
    d = len(mu)
    out = {}
    for c in itertools.product(range(N + 1), repeat=d):
        if sum(c) != N:
            continue
        F = [i for i in range(d) if c[i] > 0]
        # W(m) for all m by listing the words in F with no letter repeated consecutively
        Wm = {}

        def extend(word, counts):
            key = tuple(counts)
            if all(counts[i] >= 1 for i in range(len(F))):
                w = mu[F[word[0]]]
                for a, b in zip(word, word[1:]):
                    w *= Q[F[a]][F[b]]
                Wm[key] = Wm.get(key, 0) + w
            for j in range(len(F)):
                if word and j == word[-1]:
                    continue
                if counts[j] + 1 > c[F[j]]:
                    continue
                if word and Q[F[word[-1]]][F[j]] == 0:
                    continue
                counts[j] += 1
                extend(word + [j], counts)
                counts[j] -= 1
        extend([], [0] * len(F))
        tot = 0
        for m, w in Wm.items():
            M = sum(m)
            term = w * h ** (M - 1)
            for j, i in enumerate(F):
                term *= math.comb(c[i] - 1, m[j] - 1) * (1 + h * Q[i][i]) ** (c[i] - m[j])
            tot += term
        if tot:
            out[c] = tot
    return out


# ---------------------------------------------------------------- the rate I_F

def perron(M):
    w, V = np.linalg.eig(M)
    i = int(np.argmax(w.real))
    r = np.abs(V[:, i].real)
    w2, V2 = np.linalg.eig(M.T)
    l = np.abs(V2[:, int(np.argmax(w2.real))].real)
    return w[i].real, r, l / (l @ r)


def I_sup_u(Q, F, alpha):
    """Method A: sup over u > 0 of sum alpha_i (-(Q_F u)_i / u_i), by Newton in log u (concave)."""
    F = list(F)
    QF = Q[np.ix_(F, F)].astype(float)
    A = QF - np.diag(np.diag(QF))
    q = -np.diag(QF)
    al = np.asarray(alpha, float)
    k = len(F)
    w = np.zeros(k)
    for _ in range(200):
        E = al[:, None] * A * np.exp(w[None, :] - w[:, None])
        g = E.sum(0) - E.sum(1)
        if np.max(np.abs(g[1:])) < 1e-14:
            break
        H = -(E + E.T)
        np.fill_diagonal(H, 0)
        np.fill_diagonal(H, -H.sum(1))
        keep = al > 0
        keep[0] = False
        idx = np.where(keep)[0]
        if len(idx) == 0:
            break
        st = np.linalg.solve(H[np.ix_(idx, idx)], g[idx])
        w[idx] -= st
    E = A * np.exp(w[None, :] - w[:, None])
    return float(al @ (q - E.sum(1))), np.exp(w)


def I_legendre(Q, F, alpha):
    """Method B: sup over theta of <alpha, theta> - Lambda(theta), Lambda = Perron root of Q_F + diag(theta)."""
    F = list(F)
    QF = Q[np.ix_(F, F)].astype(float)
    al = np.asarray(alpha, float)
    k = len(F)
    Lam = lambda th: max(np.linalg.eigvals(QF + np.diag(th)).real)
    f = lambda x: -(al[1:] @ x - Lam(np.concatenate([[0.0], x])))
    r = minimize(f, np.zeros(k - 1), method='BFGS', options=dict(gtol=1e-12))
    r = minimize(f, r.x, method='Nelder-Mead', options=dict(xatol=1e-12, fatol=1e-15, maxiter=20000))
    return -r.fun


def admissible_faces(Q, mu):
    """Supports of all words of positive probability, found by a search over (support, last state)."""
    d = len(mu)
    seen = set()
    stack = [(frozenset([i]), i) for i in range(d) if mu[i] > 0]
    while stack:
        S, i = stack.pop()
        if (S, i) in seen:
            continue
        seen.add((S, i))
        for j in range(d):
            if j != i and Q[i][j] > 0:
                stack.append((S | {j}, j))
    return {tuple(sorted(S)) for S, i in seen}


def components(Q, F):
    """Strongly connected components of the switching graph on F."""
    F = list(F)
    reach = {i: {i} for i in F}
    changed = True
    while changed:
        changed = False
        for i in F:
            for j in F:
                if Q[i][j] > 0 and not reach[j] <= reach[i]:
                    reach[i] |= reach[j]
                    changed = True
    comps = []
    for i in F:
        C = frozenset(j for j in F if j in reach[i] and i in reach[j])
        if C not in comps:
            comps.append(C)
    return comps


def admissible_by_lemma(Q, mu, F):
    """Lemma 2.2(a): the components can be ordered C_1..C_r with mu(C_1) > 0 and an edge from C_j to C_(j+1)."""
    comps = components(Q, F)
    for order in itertools.permutations(comps):
        if sum(mu[i] for i in order[0]) <= 0:
            continue
        if all(any(Q[x][y] > 0 for x in order[j] for y in order[j + 1]) for j in range(len(order) - 1)):
            return True
    return False


def lam_face(Q, F):
    F = list(F)
    return -max(np.linalg.eigvals(Q[np.ix_(F, F)].astype(float)).real)


# ======================================================================== checks

def check_exact_law():
    print('\nLemma 2.3: the run expansion in exact arithmetic', flush=True)
    F = Fraction
    cells = {
        'NR3 (non-reversible)': ([[F(0), F(8, 5), F(1, 5), F(1, 10)], [F(1, 5), F(0), F(8, 5), F(1, 2)], [F(8, 5), F(1, 5), F(0), F(1)], [F(1), F(1), F(1), F(0)]],
                                 [F(1, 4)] * 4, F(1, 9), 6),
        'a zero rate (d = 3)': ([[F(0), F(2), F(0)], [F(1), F(0), F(3, 2)], [F(1, 2), F(1, 3), F(0)]], [F(1, 2), F(0), F(1, 2)], F(1, 7), 8),
        'star with 3 leaves': ([[F(0), F(1), F(1, 2), F(4, 5)], [F(2), F(0), F(0), F(0)], [F(3, 2), F(0), F(0), F(0)], [F(5, 2), F(0), F(0), F(0)]],
                               [F(1, 4)] * 4, F(1, 8), 7)}
    for name, (W, mu, h, N) in cells.items():
        Q = gen(W)
        lw = law_words(Q, mu, h, N)
        ld = law_dp(Q, mu, h, N)
        lr = law_runs(Q, mu, h, N)
        ok = lw == ld == lr and sum(lw.values()) == 1
        check(f'{name}, N = {N}: words = dynamic program = run expansion, total mass 1', ok, f'{len(lw)} compositions with positive probability')


def check_continuum():
    print('\nLemma 2.4: the continuum density integrates to the right probability', flush=True)
    Q = nr3()
    mu = np.full(4, 0.25)
    Fc = [0, 1, 2]
    A = Q[np.ix_(Fc, Fc)].copy()
    np.fill_diagonal(A, 0)
    q = -np.diag(Q)[Fc]
    rf = RunFace(A, q, mu[Fc], mmax=80)
    X, Wt = np.polynomial.legendre.leggauss(60)
    worst = 0.0
    for T in (1.0, 3.0, 6.0):
        # integrate f_T over the simplex in (alpha_2, alpha_3): alpha_2 = (1+x)/2, alpha_3 = (1 - alpha_2)(1+y)/2
        tot = 0.0
        for xi, wx in zip(X, Wt):
            a2 = (1 + xi) / 2
            for yi, wy in zip(X, Wt):
                a3 = (1 - a2) * (1 + yi) / 2
                a1 = 1 - a2 - a3
                tot += wx * wy * (1 - a2) / 4 * math.exp(rf.logf([a1, a2, a3], T))
        # stays in F up to time T and visits every state: inclusion-exclusion over subfaces
        prob = 0.0
        for s in range(1, 4):
            for G in itertools.combinations(Fc, s):
                G = list(G)
                prob += (-1) ** (3 - s) * float(mu[G] @ expm(T * Q[np.ix_(G, G)]) @ np.ones(s))
        worst = max(worst, abs(tot / prob - 1))
    check('integral of f_T over the face = P(stay in F up to T and visit all of F), T = 1, 3, 6', worst < 1e-9, f'max relative difference {worst:.1e}')


def check_admissible():
    print('\nLemma 2.2: admissible faces', flush=True)
    rng = np.random.default_rng(8)
    bad = 0
    count = 0
    for trial in range(150):
        d = int(rng.integers(3, 6))
        W = rng.uniform(0.2, 2, (d, d)) * (rng.uniform(size=(d, d)) < 0.45)
        sym = trial % 3 == 0
        if sym:
            W = np.where((W + W.T) > 0, rng.uniform(0.2, 2, (d, d)), 0)
        Q = gen(W)
        mu = rng.uniform(size=d) * (rng.uniform(size=d) < 0.6)
        if mu.sum() == 0:
            mu[0] = 1
        mu = mu / mu.sum()
        adm = admissible_faces(Q, mu)
        for s in range(1, d + 1):
            for F in itertools.combinations(range(d), s):
                count += 1
                bad += (F in adm) != admissible_by_lemma(Q, mu, F)
                irr = len(components(Q, F)) == 1
                if irr:
                    bad += (F in adm) != (mu[list(F)].sum() > 0)
                if sym and F in adm:
                    bad += not irr
    check('(a) listing the supports of all words = the ordering of components; (b) and (c)', bad == 0, f'{count} faces of 150 random chains, {bad} exceptions')


def check_rate():
    print('\nProposition 3.1: the rate on a face', flush=True)
    Q = nr3()
    Fc = (0, 1, 2)
    s, r, l = perron(Q[np.ix_(Fc, Fc)])
    lam = -s
    astar = l * r
    agree('NR3: lambda_F', '0.492412', {'Perron root': lam, 'I_F(alpha*), sup over u': I_sup_u(Q, Fc, astar)[0], 'I_F(alpha*), Legendre': I_legendre(Q, Fc, astar)})
    # direct minimization of I_F over the simplex, with I_F from the Legendre transform
    f = lambda x: I_legendre(Q, Fc, [1 - x[0] - x[1], x[0], x[1]]) if (x.min() > 0 and x.sum() < 1) else 1e9
    res = minimize(f, [1 / 3, 1 / 3], method='Nelder-Mead', options=dict(xatol=1e-8, fatol=1e-13))
    amin = np.array([1 - res.x.sum(), res.x[0], res.x[1]])
    for i, pr in enumerate(('0.42773', '0.32522', '0.24705')):
        agree(f'NR3: alpha*_{i + 1}', pr, {'l o r': astar[i], 'argmin of I_F': amin[i]})
    ln = l / l.sum()
    r2 = r ** 2 / (r ** 2).sum()
    Qc = Q[np.ix_(Fc, Fc)].copy()
    np.fill_diagonal(Qc, 0)
    np.fill_diagonal(Qc, -Qc.sum(1))
    w, V = np.linalg.eig(Qc.T)
    pic = np.abs(V[:, int(np.argmin(abs(w)))].real)
    pic /= pic.sum()
    agree('NR3: L1 distance from alpha* to l_F', '0.122', {'value': np.abs(astar - ln).sum()})
    agree('NR3: L1 distance from alpha* to r_F^2', '0.090', {'value': np.abs(astar - r2).sum()})
    agree('NR3: L1 distance from alpha* to the uniform law', '0.189', {'value': np.abs(astar - 1 / 3).sum()},
          f'; to the stationary law of the conservative part: {np.abs(astar - pic).sum():.4f}')
    # (a), (b) on random non-reversible faces
    rng = np.random.default_rng(4)
    worst = 0.0
    worst_stat = 0.0
    worst_min = 0.0
    for trial in range(8):
        k = int(rng.integers(2, 5))
        d = k + 1
        W = rng.uniform(0.1, 2, (d, d))
        Q = gen(W)
        F = tuple(range(k))
        s, r, l = perron(Q[np.ix_(F, F)])
        a_st = l * r
        worst_min = max(worst_min, abs(I_sup_u(Q, F, a_st)[0] + s))
        for _ in range(3):
            al = rng.dirichlet(np.ones(k))
            IA, u = I_sup_u(Q, F, al)
            IB = I_legendre(Q, F, al)
            worst = max(worst, abs(IA - IB))
            worst_min = max(worst_min, max(0, -(IA + s)))          # I_F >= lambda_F
            QF = Q[np.ix_(F, F)]
            G = QF * u[None, :] / u[:, None]
            np.fill_diagonal(G, 0)
            np.fill_diagonal(G, -G.sum(1))
            worst_stat = max(worst_stat, np.abs(al @ G).max())
    check('(a) I_F >= lambda_F with equality at l o r; sup over u = Legendre transform', worst < 1e-8 and worst_min < 1e-10,
          f'max |A - B| = {worst:.1e}, max violation {worst_min:.1e} (24 random points of 8 random faces)')
    check('(b) at the maximizing u, alpha is stationary for the tilted generator', worst_stat < 1e-10, f'max |alpha^T G| = {worst_stat:.1e}')
    # (c) reversible faces, including points on the boundary of the simplex
    worst = 0.0
    for trial in range(8):
        k = int(rng.integers(2, 5))
        d = k + 1
        nu = rng.uniform(0.5, 2, d)
        S = rng.uniform(0.2, 2, (d, d))
        S = S + S.T
        Q = gen(S / nu[:, None])
        F = tuple(range(k))
        qout = np.array([sum(Q[i, j] for j in range(d) if j not in F) for i in F])
        for _ in range(3):
            al = rng.dirichlet(np.ones(k))
            if _ == 2:
                al[0] = 0
                al /= al.sum()
            closed = sum((math.sqrt(al[i] * Q[F[i], F[j]]) - math.sqrt(al[j] * Q[F[j], F[i]])) ** 2 for i in range(k) for j in range(i + 1, k)) + al @ qout
            keep = [i for i in range(k) if al[i] > 0]
            sub = [F[i] for i in keep]
            if len(keep) == k:
                nums = [I_sup_u(Q, F, al)[0], I_legendre(Q, F, al)]
            elif len(keep) > 1:
                # on the boundary the rate is that of the subface (part (d)), with the full exit rates
                nums = [I_sup_u(Q, sub, al[keep])[0], I_legendre(Q, sub, al[keep])]
            else:
                nums = [float(-Q[sub[0], sub[0]])]
            worst = max(worst, max(abs(v - closed) for v in nums))
    check('(c) the reversible closed form, also on the boundary', worst < 1e-7, f'max difference {worst:.1e}')
    # (d) subfaces
    worst = 0.0
    strict = True
    for trial in range(6):
        d = 5
        Q = gen(rng.uniform(0.1, 2, (d, d)))
        F = (0, 1, 2, 3)
        Fp = (0, 1)
        al = rng.dirichlet(np.ones(2))
        IA = I_sup_u(Q, Fp, al)[0]
        IB = I_legendre(Q, Fp, al)
        # I_F is continuous on the closed face, so I_F at nearby interior points must tend to I_F'(alpha)
        near = []
        for eps in (1e-6, 1e-8, 1e-10):
            pt = np.array([al[0], al[1], eps, eps])
            near.append(I_sup_u(Q, F, pt / pt.sum())[0])
        # the approach is like sqrt(eps), so extrapolate in sqrt(eps) from eps = 1e-8 and 1e-10
        limit = (10 * near[2] - near[1]) / 9
        worst = max(worst, abs(IA - IB), abs(limit - IA))
        strict &= lam_face(Q, Fp) > lam_face(Q, F) and IA >= lam_face(Q, Fp) - 1e-12
    check('(d) I_F = I_F\' on the subface, and I_F\' >= lambda_F\' > lambda_F', worst < 1e-6 and strict,
          f'max difference {worst:.1e} (I_F at interior points near the subface, extrapolated in sqrt(eps); I_F\' by both methods)')


def check_star():
    print('\nSection 8: the zero set of the star', flush=True)
    for leaves, N in ((3, 7), (4, 7)):
        d = leaves + 1
        W = [[Fraction(0)] * d for _ in range(d)]
        for j in range(1, d):
            W[0][j] = Fraction(j, 2)
            W[j][0] = Fraction(3, j + 1)
        Q = gen(W)
        mu = [Fraction(1, d)] * d
        law = law_dp(Q, mu, Fraction(1, 10), N)
        bad = 0
        for c in itertools.product(range(1, N + 1), repeat=d):
            if sum(c) != N:
                continue
            p = law.get(c, 0)
            bad += (p == 0) != (c[0] < leaves - 1)
        check(f'{leaves} leaves, N = {N}: P_N(n) = 0 exactly when the center count is below {leaves - 1}', bad == 0, f'{bad} exceptions')


def hull_winners(lams):
    """Method A: the lower-left hull of the points (lambda_F, |F|-1), read from right to left."""
    pts = sorted({(round(l, 12), len(F) - 1) for F, l in lams.items()}, key=lambda p: (p[1], p[0]))
    best = {}
    for x, y in pts:
        best[y] = min(best.get(y, np.inf), x)
    ys = sorted(best)
    chain = [(best[ys[0]], ys[0])]
    for y in ys[1:]:
        x = best[y]
        if x >= chain[-1][0] - 1e-12:
            continue
        chain.append((x, y))
        while len(chain) >= 3:
            (x1, y1), (x2, y2), (x3, y3) = chain[-3:]
            # keep the middle point only if the slope decreases in magnitude (convex from the right)
            if (y2 - y1) / (x1 - x2) >= (y3 - y2) / (x2 - x3) - 1e-12:
                chain.pop(-2)
            else:
                break
    taus = [(y2 - y1) / (x1 - x2) for (x1, y1), (x2, y2) in zip(chain, chain[1:])]
    return chain, taus


def check_hull():
    print('\nTheorem 3.4 and the remark after it: the geometry of the winners', flush=True)
    rng = np.random.default_rng(12)
    bad = 0
    total = 0
    for trial in range(120):
        d = int(rng.integers(3, 6))
        sym = trial % 2 == 0
        W = rng.uniform(0.2, 2, (d, d)) * (rng.uniform(size=(d, d)) < 0.7)
        if sym:
            W = np.triu(W, 1) + np.triu(W, 1).T
        Q = gen(W)
        mu = np.full(d, 1 / d) if trial % 3 else rng.dirichlet(np.ones(d)) * (rng.uniform(size=d) < 0.7)
        if mu.sum() == 0:
            mu[0] = 1
        mu = mu / mu.sum()
        adm = admissible_faces(Q, mu)
        lams = {F: lam_face(Q, F) for F in adm}
        chain, taus = hull_winners(lams)
        # method B: direct minimization on a grid of tau between and around the switch values
        grid = sorted(set(np.concatenate([np.geomspace(1e-3, 1e3, 400)] + [[t * 0.999, t * 1.001] for t in taus])))
        prevF = None
        for t in grid:
            costs = {F: t * l + len(F) - 1 for F, l in lams.items()}
            m = min(costs.values())
            winners = [F for F, c in costs.items() if c <= m + 1e-10]
            total += 1
            pt = {(round(lams[F], 12), len(F) - 1) for F in winners}
            # the winning point must be the hull vertex active at this tau
            k = sum(1 for s in taus if s < t)
            bad += pt != {(round(chain[k][0], 12), chain[k][1])}
            if prevF is not None:                     # (b): lambda does not increase, size does not decrease
                bad += not (lams[winners[0]] <= lams[prevF] + 1e-12 and len(winners[0]) >= len(prevF))
            prevF = winners[0]
            if sym or mu.min() > 0:                   # (c)
                bad += any(len(components(Q, F)) > 1 for F in winners)
    check('(a), (b), (c): winners = hull vertices, monotone in tau, irreducible under (a) or (b)', bad == 0, f'{total} (chain, tau) pairs, {bad} exceptions')
    # the remark after Theorem 3.4 (symmetric Q)
    bad = 0
    for trial in range(60):
        d = int(rng.integers(3, 7))
        W = rng.uniform(0.2, 2, (d, d))
        W = np.triu(W, 1) + np.triu(W, 1).T
        W *= rng.uniform(size=(d, d)) < 0.8
        W = np.triu(W, 1) + np.triu(W, 1).T
        for i in range(d - 1):
            W[i, i + 1] = W[i + 1, i] = max(W[i, i + 1], 0.3)
        Q = gen(W)
        for s in range(1, d + 1):
            for F in itertools.combinations(range(d), s):
                F = list(F)
                lamF = lam_face(Q, F)
                # (a) the least Dirichlet form over unit vectors supported in F (random search as a lower check)
                v = np.linalg.eigh(-Q[np.ix_(F, F)])[1][:, 0]
                bad += abs(v @ (-Q[np.ix_(F, F)]) @ v - lamF) > 1e-10
                for _ in range(3):
                    x = rng.normal(size=s)
                    x /= np.linalg.norm(x)
                    bad += x @ (-Q[np.ix_(F, F)]) @ x < lamF - 1e-12
        mu_s = [min(lam_face(Q, list(F)) for F in itertools.combinations(range(d), s)) for s in range(1, d + 1)]
        bad += not all(a > b for a, b in zip(mu_s, mu_s[1:])) or abs(mu_s[-1]) > 1e-10
    check('after Theorem 3.4: lambda_F is the least Dirichlet form, and mu_1 > mu_2 > ... > mu_d = 0', bad == 0, f'{bad} exceptions in 60 random symmetric generators')


def check_face_order(full):
    print('\nFirst-order selection at finite N (the star S3a and the path P4b of ledger_C1.md)', flush=True)
    cells = {'star S3a': (star((1.0, 2.0, 0.5, 1.5, 0.8, 2.5)), {64: ((2,), (0, 1), (0, 1, 3), (0, 1, 2, 3), ('3.482', '5.321', '9.264')),
                                                                  160: ((2,), (0, 1), (0, 1, 3), (0, 1, 2, 3), ('4.573', '7.065', '12.314'))}),
             'path P4b': (path((3.0, 1.2, 1.5, 2.0, 1.5, 3.0)), {64: ((1,), (0, 1), (0, 1, 2), (0, 1, 2, 3), ('1.683', '4.198', '6.515')),
                                                                  160: ((1,), (0, 1), (0, 1, 2), (0, 1, 2, 3), ('2.158', '5.618', '8.694'))})}
    mu = np.full(4, 0.25)
    for name, (Q, runs) in cells.items():
        # the first-order prediction from the hull
        adm = admissible_faces(Q, mu)
        chain, taus = hull_winners({F: lam_face(Q, F) for F in adm})
        for N, (*order, printed) in runs.items():
            if N > 64 and not full:
                continue
            fm = {}
            x0 = {}
            for F in order:
                A = Q[np.ix_(F, F)].copy()
                np.fill_diagonal(A, 0)
                mm = {1: 1, 2: N, 3: min(N, 100), 4: min(N, 36)}[len(F)]
                fm[F] = (RunFace(A, -np.diag(Q)[list(F)], mu[list(F)], mmax=mm) if len(F) > 1 else None, F)

            def logM(F, T):
                rf, _ = fm[F]
                h = T / N
                k = len(F)
                if k == 1:
                    return log(0.25) + (N - 1) * math.log1p(h * Q[F[0], F[0]])
                if k == 2:
                    return max(rf.logP([a, N - a], h) for a in range(1, N))
                f = lambda x: -rf.logP(N * np.concatenate([[1 - x.sum()], x]), h) if (x.min() > 0 and x.sum() < 1) else 1e300
                x = minimize(f, x0.get(F, np.full(k - 1, 1 / k)), method='Nelder-Mead', options=dict(xatol=1e-7, fatol=1e-12)).x
                x0[F] = x
                c = np.round(N * x).astype(int)
                best = -np.inf
                rad = 2 if k == 3 else 1
                for off in itertools.product(range(-rad, rad + 1), repeat=k - 1):
                    tail = c + np.array(off)
                    if tail.min() >= 1 and N - tail.sum() >= 1:
                        best = max(best, rf.logP([N - tail.sum()] + list(tail), h))
                return best
            # each switch is bracketed within 25% of the recorded value, and a missing sign change is a failure
            Ts = []
            for (a, b), pr in zip(zip(order, order[1:]), printed):
                try:
                    Ts.append(brentq(lambda T: logM(b, T) - logM(a, T), 0.8 * float(pr), 1.25 * float(pr), xtol=1e-8))
                except ValueError:
                    Ts.append(float('nan'))
            # method A: the full dynamic program changes its mode support at each of these T
            if any(np.isnan(Ts)):
                check(f'{name}, N = {N}: switches found', False, f'no sign change within 25% of a recorded switch: {Ts}')
                continue
            probe = [T + e for T in Ts for e in (-2e-4, 2e-4)]
            probs, comps = full_law(Q, N, probe)
            sups = [tuple(i for i in range(4) if comps[int(np.argmax(probs[:, t]))][i] > 0) for t in range(len(probe))]
            want = [order[0], order[1], order[1], order[2], order[2], order[3]]
            check(f'{name}, N = {N}: the mode goes {" -> ".join(str(F) for F in order)} (full dynamic program at T -+ 2e-4)',
                  sups == want, f'supports {sups}; first-order switch values tau* log N = {np.round(np.array(taus[:3]) * log(N), 3)}')
            for i, (T, pr) in enumerate(zip(Ts, printed)):
                agree(f'{name}, N = {N}: switch {i + 1}', pr, {'face maxima': T})


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--full', action='store_true', help='also run the cells at N = 160')
    args = parser.parse_args()
    t0 = time.time()
    for step in (check_exact_law, check_continuum, check_admissible, check_rate, check_star, check_hull, lambda: check_face_order(args.full)):
        t1 = time.time()
        step()
        print(f'  ({time.time() - t1:.0f} s)', flush=True)
    print(f'\nverify_first_order: {len(FAILS)} failures, {time.time() - t0:.0f} s', flush=True)
    if FAILS:
        print('failed: ' + '; '.join(FAILS))
        sys.exit(1)


if __name__ == '__main__':
    main()
