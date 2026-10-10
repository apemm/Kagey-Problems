"""Checks for the section on entropy production.

1. The entropy production rate sigma(mu, G) is recovered from the function
   r(lambda) = mu^T (Lambda - G)^(-1) 1 alone, used as a black box, through the
   pair data mu_i, q_i, c_ij, a_ij. Stationary and other starts, d = 3, 4, 5.
2. Chains with the same counts have the same sigma: a chain and its reversal
   (stationary start), and the two chains of the four-state example.
3. The size of the affinity of every triangle is recovered from the principal
   minors of G of orders 1, 2 and 3, and it is the same for a chain and its
   reversal.
"""
import itertools
from math import log, sqrt

import numpy as np

rng = np.random.default_rng(11)
BIG = 1e10


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


def sigma_true(mu, G):
    d = len(G)
    s = 0.0
    for i in range(d):
        for j in range(i + 1, d):
            f, g = mu[i] * G[i, j], mu[j] * G[j, i]
            if f > 0 and g > 0:
                s += (f - g) * log(f / g)
    return s


def sigma_from_r(r, d):
    """Entropy production from the black box r, by the recipe of the note."""
    def killed(F, lam_F):
        lam = np.full(d, BIG)
        lam[list(F)] = lam_F
        return r(lam)

    mu, q = np.zeros(d), np.zeros(d)
    for i in range(d):
        r1, r2 = killed([i], [1.0]), killed([i], [2.0])      # r = mu/(lam + q)
        q[i] = (2 * r2 - r1) / (r1 - r2)
        mu[i] = r1 * (1 + q[i])
    s = 0.0
    for i in range(d):
        for j in range(i + 1, d):
            rows, rhs = [], []
            for li, lj in ((1.0, 2.0), (3.0, 1.5)):
                xi, xj = li + q[i], lj + q[j]
                rv = killed([i, j], [li, lj])
                rows.append([1.0, rv])                        # c + r a = r xi xj - mu_i xj - mu_j xi
                rhs.append(rv * xi * xj - mu[i] * xj - mu[j] * xi)
            c, a = np.linalg.solve(np.array(rows), np.array(rhs))
            J2 = max(c * c - 4 * mu[i] * mu[j] * a, 0.0)
            J = sqrt(J2)
            if J > 1e-7:
                s += J * log((c + J) / (c - J))
    return s


def affinities(G):
    """|A_ijk| for every triangle, from principal minors of orders 1, 2, 3 only."""
    d = len(G)
    q = -np.diag(G)
    out = []
    for i, j, k in itertools.combinations(range(d), 3):
        a = {frozenset(p): q[p[0]] * q[p[1]] - np.linalg.det(-G[np.ix_(p, p)])
             for p in ((i, j), (j, k), (i, k))}
        m3 = np.linalg.det(-G[np.ix_((i, j, k), (i, j, k))])
        s = (q[i] * q[j] * q[k] - q[i] * a[frozenset((j, k))] - q[j] * a[frozenset((i, k))]
             - q[k] * a[frozenset((i, j))] - m3)                 # w + wbar
        p = a[frozenset((i, j))] * a[frozenset((j, k))] * a[frozenset((i, k))]   # w * wbar
        disc = sqrt(max(s * s - 4 * p, 0.0))
        out.append(abs(log((s + disc) / (s - disc))) if s - disc > 0 else float("inf"))
    return np.array(out)


def affinities_true(G):
    d = len(G)
    return np.array([abs(log(G[i, j] * G[j, k] * G[k, i] / (G[i, k] * G[k, j] * G[j, i])))
                     for i, j, k in itertools.combinations(range(d), 3)])


ok = True
print("1. sigma from the black box r")
for d in (3, 4, 5):
    for kind in ("stationary", "other"):
        G = gen(rng.uniform(0.2, 2.0, (d, d)))
        mu = stat(G)
        if kind == "other":
            mu = rng.uniform(0.5, 1.5, d)
            mu /= mu.sum()
        r = lambda lam, mu=mu, G=G: mu @ np.linalg.solve(np.diag(lam) - G, np.ones(len(G)))
        a, b = sigma_true(mu, G), sigma_from_r(r, d)
        ok = ok and abs(a - b) < 1e-4   # limited by the finite killing rate BIG
        print("   d = %d, %-10s start: sigma = %.8f, from r = %.8f" % (d, kind, a, b))

print("2. chains with the same counts have the same sigma")
for d in (3, 4, 5):
    G = gen(rng.uniform(0.2, 2.0, (d, d)))
    pi = stat(G)
    Gh = gen(G.T * pi[None, :] / pi[:, None])
    ok = ok and abs(sigma_true(pi, G) - sigma_true(pi, Gh)) < 1e-12
    print("   d = %d: chain %.10f, reversal %.10f" % (d, sigma_true(pi, G), sigma_true(pi, Gh)))
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


mu4 = np.array([mub[0], mub[1], mub[2] * nu[0], mub[2] * nu[1]])
s1, s2 = sigma_true(mu4, lift(Lg)), sigma_true(mu4, lift(Lr))
ok = ok and abs(s1 - s2) < 1e-12
print("   four-state example (start not stationary): G %.10f, G' %.10f" % (s1, s2))

print("3. triangle affinities from principal minors of orders 1, 2, 3")
for d in (3, 4, 5):
    G = gen(rng.uniform(0.2, 2.0, (d, d)))
    pi = stat(G)
    Gh = gen(G.T * pi[None, :] / pi[:, None])
    e1 = abs(affinities(G) - affinities_true(G)).max()
    e2 = abs(affinities(G) - affinities(Gh)).max()
    ok = ok and e1 < 1e-6 and e2 < 1e-6
    print("   d = %d: error %.1e, chain against reversal %.1e" % (d, e1, e2))
print("all checks passed:", ok)
if not ok:
    raise SystemExit(1)
