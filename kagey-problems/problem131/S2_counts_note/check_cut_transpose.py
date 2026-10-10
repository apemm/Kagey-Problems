"""Ties and the cut-transpose.

Chatterjee, Ghosh, Gurjar and Raj show that two irreducible matrices have the
same principal minors exactly when one is reached from the other by transposes
across cuts and diagonal equivalence. This script asks what that means for
chains.

1. The lumped reversal of the four-state example is the cut-transpose across
   the module, up to a diagonal similarity.
2. A cut-transpose of a rate matrix across ANY cut is diagonally similar to a
   rate matrix G' with the same principal minors as G.
3. But G' has the same counts as G only if the second set of minors (those of
   G - 1 mu^T) also agrees. For a cut that is not a module this fails, with a
   stationary start and with other starts.
4. Discrete time: the laws of the count vector at all horizons determine the
   principal minors of P and of P - 1 mu^T (checked through the generating
   function), and a chain and its reversal agree.
"""
import itertools

import numpy as np
from scipy.linalg import expm, null_space

rng = np.random.default_rng(5)


def gen(A):
    A = np.array(A, dtype=float)
    np.fill_diagonal(A, 0.0)
    return A - np.diag(A.sum(1))


def stat(G):
    d = len(G)
    M = np.vstack([G.T[:-1], np.ones(d)])
    b = np.zeros(d)
    b[-1] = 1
    return np.linalg.solve(M, b)


def minors_gap(A, B):
    d = len(A)
    worst = 0.0
    for k in range(1, d + 1):
        for U in itertools.combinations(range(d), k):
            U = list(U)
            worst = max(worst, abs(np.linalg.det(A[np.ix_(U, U)]) - np.linalg.det(B[np.ix_(U, U)])))
    return worst


def law_gap(mu, G, mu2, G2, trials=40):
    d = len(G)
    worst = 0.0
    for _ in range(trials):
        lam = rng.uniform(0.0, 3.0, d)
        t = rng.choice([0.3, 1.0, 4.0])
        a = mu @ expm(t * (G - np.diag(lam))) @ np.ones(d)
        b = mu2 @ expm(t * (G2 - np.diag(lam))) @ np.ones(d)
        worst = max(worst, abs(a - b))
    return worst


def cut_transpose(G, X):
    """ct(G, X): with G = [[M, p q^T], [u v^T, N]] return [[M, p u^T], [q v^T, N^T]]."""
    d = len(G)
    Y = [i for i in range(d) if i not in X]
    A, B = G[np.ix_(X, Y)], G[np.ix_(Y, X)]
    ua, sa, va = np.linalg.svd(A)
    ub, sb, vb = np.linalg.svd(B)
    assert sa[1] < 1e-10 and sb[1] < 1e-10, "not a cut"
    p, q = ua[:, 0] * sa[0], va[0]
    u, v = ub[:, 0] * sb[0], vb[0]
    C = np.zeros_like(G)
    C[np.ix_(X, X)] = G[np.ix_(X, X)]
    C[np.ix_(Y, Y)] = G[np.ix_(Y, Y)].T
    C[np.ix_(X, Y)] = np.outer(p, u)
    C[np.ix_(Y, X)] = np.outer(q, v)
    return C


def to_generator(C):
    """A positive w with C w = 0 gives the rate matrix W^-1 C W."""
    w = null_space(C)[:, 0]
    w = w * np.sign(w[0])
    assert (w > 0).all(), "no positive kernel vector"
    return gen(C * w[None, :] / w[:, None])


ok = True
print("1. the lumped reversal of the four-state example is a cut-transpose")
Lg = gen([[0, 0.9, 0.5], [0.3, 0, 1.1], [0.8, 0.4, 0]])
mub = stat(Lg)
nu = np.array([0.35, 0.65])
Lr = gen(Lg.T * mub[None, :] / mub[:, None])


def lift(Lc):
    G = np.zeros((4, 4))
    G[0, 1], G[1, 0] = Lc[0, 1], Lc[1, 0]
    for x in (0, 1):
        G[x, 2], G[x, 3] = Lc[x, 2] * nu
        G[2, x] = G[3, x] = Lc[2, x]
    G[2, 3], G[3, 2] = 1.7, 0.2
    return gen(G)


G, G2 = lift(Lg), lift(Lr)
mu = np.array([mub[0], mub[1], mub[2] * nu[0], mub[2] * nu[1]])
Gct = to_generator(cut_transpose(G, [2, 3]))
e = abs(Gct - G2).max()
ok = ok and e < 1e-9
print("   max |W^-1 ct(G, module) W - G'| = %.1e" % e)

print("2, 3. a cut that is not a module")
for trial in range(3):
    d = 4
    X, Y = [0, 1], [2, 3]
    A = rng.uniform(0.2, 2.0, (d, d))
    A[np.ix_(X, Y)] = np.outer(rng.uniform(0.3, 1.5, 2), rng.uniform(0.3, 1.5, 2))
    A[np.ix_(Y, X)] = np.outer(rng.uniform(0.3, 1.5, 2), rng.uniform(0.3, 1.5, 2))
    G = gen(A)
    Gp = to_generator(cut_transpose(G, X))
    pi, pip = stat(G), stat(Gp)
    m1 = minors_gap(G, Gp)
    one = np.ones(d)
    m2 = minors_gap(G - np.outer(one, pi), Gp - np.outer(one, pi))
    gap_stat = law_gap(pi, G, pip, Gp)
    gap_same = law_gap(pi, G, pi, Gp)
    ok = ok and m1 < 1e-9
    print("   trial %d: minors of G agree to %.1e; |pi - pi'| = %.3f; minors of G - 1 pi^T differ by %.2e;"
          % (trial, m1, abs(pi - pip).max(), m2))
    print("            law gap with each chain stationary %.2e, with the same start pi %.2e" % (gap_stat, gap_same))

print("4. discrete time: generating function and principal minors")
for d in (3, 4):
    P = rng.uniform(0.1, 1.0, (d, d))
    P /= P.sum(1, keepdims=True)
    mu = rng.uniform(0.5, 1.5, d)
    mu /= mu.sum()
    y = rng.uniform(0.05, 0.3, d)
    Dy = np.diag(y)
    den = np.linalg.det(np.eye(d) - P @ Dy)
    num = np.linalg.det(np.eye(d) - P @ Dy + np.outer(np.ones(d), mu) @ Dy) - den
    series = sum(mu @ Dy @ np.linalg.matrix_power(P @ Dy, n) @ np.ones(d) for n in range(400))
    exp_den = sum((-1) ** len(S) * np.prod(y[list(S)]) * np.linalg.det(P[np.ix_(S, S)])
                  for k in range(d + 1) for S in itertools.combinations(range(d), k))
    Pm = P - np.outer(np.ones(d), mu)
    exp_sum = sum((-1) ** len(S) * np.prod(y[list(S)]) * np.linalg.det(Pm[np.ix_(S, S)])
                  for k in range(d + 1) for S in itertools.combinations(range(d), k))
    e1, e2, e3 = abs(series - num / den), abs(den - exp_den), abs(den + num - exp_sum)
    ok = ok and max(e1, e2, e3) < 1e-10
    print("   d = %d: sum over horizons = num/den to %.1e; den = sum of minors of P to %.1e;"
          " den + num = sum of minors of P - 1 mu^T to %.1e" % (d, e1, e2, e3))
print("all exact checks passed:", ok)
if not ok:
    raise SystemExit(1)
