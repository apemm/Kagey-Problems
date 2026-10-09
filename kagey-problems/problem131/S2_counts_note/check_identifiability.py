"""S2 checks: which generators are recoverable from occupation-time laws.

Phi(lam) = mu^T expm(G - diag(lam)) 1 is the Laplace transform of the occupation
vector L on [0,1] of the chain with generator G and start law mu.
"""
import itertools
import numpy as np
from scipy.linalg import expm

rng = np.random.default_rng(7)


def rand_gen(d, lo=0.3, hi=2.0):
    G = rng.uniform(lo, hi, (d, d))
    np.fill_diagonal(G, 0.0)
    np.fill_diagonal(G, -G.sum(1))
    return G


def stat(G):
    d = len(G)
    A = np.vstack([G.T, np.ones(d)])
    b = np.zeros(d + 1)
    b[-1] = 1
    return np.linalg.lstsq(A, b, rcond=None)[0]


def phi(mu, G, lam):
    return mu @ expm(G - np.diag(lam)) @ np.ones(len(G))


def maxdiff(mu1, G1, mu2, G2, trials=40, scale=3.0):
    d = len(G1)
    worst = 0.0
    for _ in range(trials):
        lam = rng.uniform(0, scale, d)
        a, b = phi(mu1, G1, lam), phi(mu2, G2, lam)
        worst = max(worst, abs(a - b) / abs(a))
    return worst


def reversal(mu, G):
    return (G.T * mu[None, :]) / mu[:, None]


print("1. reversal with stationary start (should be ~1e-15)")
for d in (3, 4, 5):
    G = rand_gen(d)
    pi = stat(G)
    Gr = reversal(pi, G)
    print("   d=%d  rowsum err %.1e  law diff %.1e  |G-Gr| %.2f" % (
        d, abs(Gr.sum(1)).max(), maxdiff(pi, G, pi, Gr), abs(G - Gr).max()))

print("2. reversal formula with a non-stationary start is not a generator")
G = rand_gen(3)
mu = np.array([0.5, 0.3, 0.2])
print("   row sums of M^-1 G^T M:", np.round(reversal(mu, G).sum(1), 3))


def jac_rank(d, mode, npts=None, tol=1e-7):
    """Rank of d Phi / d params at a random point, by central differences."""
    G0 = rand_gen(d)
    offs = [(i, j) for i in range(d) for j in range(d) if i != j]
    if mode == "known":
        mu0 = rng.dirichlet(np.ones(d) * 3)
    elif mode == "delta":
        mu0 = np.zeros(d)
        mu0[0] = 1
    npts = npts or 6 * d * d
    lams = rng.uniform(-1.0, 4.0, (npts, d))

    def build(theta):
        G = np.zeros((d, d))
        for (i, j), t in zip(offs, theta):
            G[i, j] = t
        np.fill_diagonal(G, -G.sum(1))
        return G

    def F(theta):
        G = build(theta)
        mu = stat(G) if mode == "stationary" else mu0
        return np.array([phi(mu, G, l) for l in lams])

    th0 = np.array([G0[i, j] for i, j in offs])
    h = 1e-5
    J = np.zeros((npts, len(th0)))
    for k in range(len(th0)):
        e = np.zeros(len(th0))
        e[k] = h
        J[:, k] = (F(th0 + e) - F(th0 - e)) / (2 * h)
    s = np.linalg.svd(J, compute_uv=False)
    return int((s > tol * s[0]).sum()), len(th0), s[-3:] / s[0]


print("3. Jacobian rank of G -> law (full rank means locally identifiable)")
for d in (2, 3, 4):
    for mode in ("known", "stationary", "delta"):
        r, n, tail = jac_rank(d, mode)
        print("   d=%d %-10s rank %d of %d   smallest sv ratios %s" % (
            d, mode, r, n, np.array2string(tail, precision=1)))


def rev_gen(d):
    """Random reversible generator: g_ij = s_ij / pi_i with s symmetric."""
    pi = rng.dirichlet(np.ones(d) * 3)
    S = rng.uniform(0.3, 2.0, (d, d))
    S = (S + S.T) / 2
    G = S / pi[:, None]
    np.fill_diagonal(G, 0.0)
    np.fill_diagonal(G, -G.sum(1))
    return pi, G


print("4. stationary start AT a reversible chain: rank drops by (d-1)(d-2)/2")
for d in (3, 4, 5):
    pi, G0 = rev_gen(d)
    offs = [(i, j) for i in range(d) for j in range(d) if i != j]
    npts = 6 * d * d
    lams = rng.uniform(-1.0, 4.0, (npts, d))

    def build(theta):
        G = np.zeros((d, d))
        for (i, j), t in zip(offs, theta):
            G[i, j] = t
        np.fill_diagonal(G, -G.sum(1))
        return G

    def F(theta):
        G = build(theta)
        return np.array([phi(stat(G), G, l) for l in lams])

    th0 = np.array([G0[i, j] for i, j in offs])
    h = 1e-5
    J = np.zeros((npts, len(th0)))
    for k in range(len(th0)):
        e = np.zeros(len(th0))
        e[k] = h
        J[:, k] = (F(th0 + e) - F(th0 - e)) / (2 * h)
    s = np.linalg.svd(J, compute_uv=False)
    r = int((s > 1e-6 * s[0]).sum())
    print("   d=%d rank %d of %d, predicted nullity %d, got %d" % (
        d, r, len(th0), (d - 1) * (d - 2) // 2, len(th0) - r))

print("5. pair data: flipping one unbalanced edge keeps a_ij and c_ij but changes the law")
d = 4
G = rand_gen(d)
mu = rng.dirichlet(np.ones(d) * 3)
G2 = G.copy()
i, j = 0, 1
G2[i, j] = mu[j] * G[j, i] / mu[i]
G2[j, i] = mu[i] * G[i, j] / mu[j]
print("   a same:", np.isclose(G[i, j] * G[j, i], G2[i, j] * G2[j, i]),
      " c same:", np.isclose(mu[i] * G[i, j] + mu[j] * G[j, i], mu[i] * G2[i, j] + mu[j] * G2[j, i]))
np.fill_diagonal(G2, 0.0)
np.fill_diagonal(G2, -G2.sum(1))
print("   law diff after the flip (rows re-normalized): %.2e" % maxdiff(mu, G, mu, G2))


def bowtie(nB, stationary_B):
    """States: v=0, A0 = {1,2}, B0 = {3..}.  Block A is a triangle on which mu solves the
    stationarity equations at 1 and 2.  Every state of B0 returns to v at the same rate gam,
    and v enters B0 in proportion to mu."""
    d = 3 + nB
    v, A0, B0 = 0, [1, 2], list(range(3, 3 + nB))
    G = np.zeros((d, d))
    gam = 0.9
    for x in B0:
        G[x, v] = gam
    for x in B0:
        for y in B0:
            if x != y:
                G[x, y] = rng.uniform(0.3, 2.0)
    G[v, 1], G[v, 2] = 0.8, 0.35
    G[1, 2], G[2, 1] = 1.3, 0.4
    G[1, v], G[2, v] = 0.5, 1.1
    # mu on A: stationarity at the two interior states of A, with mu_v = 1 (rescaled later)
    q1 = G[1, 2] + G[1, v]
    q2 = G[2, 1] + G[2, v]
    M = np.array([[q1, -G[2, 1]], [-G[1, 2], q2]])
    muA = np.linalg.solve(M, np.array([G[v, 1], G[v, 2]]))
    mu = np.zeros(d)
    mu[v] = 1.0
    mu[1], mu[2] = muA
    if stationary_B:
        Gi = G[np.ix_(B0, B0)].copy()
        np.fill_diagonal(Gi, -Gi.sum(1))
        m = stat(Gi)
        mu[B0] = 0.7 * m
    else:
        mu[B0] = rng.uniform(0.2, 1.0, nB)
    for x in B0:
        G[v, x] = gam * mu[x] / mu[v]
    mu = mu / mu.sum()
    np.fill_diagonal(G, 0.0)
    np.fill_diagonal(G, -G.sum(1))
    return mu, G, [v] + A0, [v] + B0


def partial_reverse(mu, G, block):
    G2 = G.copy()
    for i in block:
        for j in block:
            if i != j:
                G2[i, j] = mu[j] * G[j, i] / mu[i]
    np.fill_diagonal(G2, 0.0)
    rs = G2.sum(1)
    np.fill_diagonal(G2, np.diag(G))
    return G2, rs + np.diag(G)


print("6. block reversal at a cut state")
for nB, statB in ((2, False), (3, True), (3, False)):
    mu, G, A, B = bowtie(nB, statB)
    GA, errA = partial_reverse(mu, G, A)
    print("   nB=%d stationaryB=%s  mu stationary? %.1e" % (nB, statB, abs(mu @ G).max()))
    print("      reverse A: rowsum err %.1e  |G-GA| %.2f  law diff %.1e" % (
        abs(errA).max(), abs(G - GA).max(), maxdiff(mu, G, mu, GA)))
    if statB:
        GB, errB = partial_reverse(mu, G, B)
        Gr = reversal(mu, G)
        print("      reverse B: rowsum err %.1e  |G-GB| %.2f  law diff %.1e" % (
            abs(errB).max(), abs(G - GB).max(), maxdiff(mu, G, mu, GB)))
        print("      full reversal law diff %.1e ; GA vs full reversal |.| %.2f" % (
            maxdiff(mu, G, mu, Gr), abs(GA - Gr).max()))

print("7. control: same bowtie but unequal return rates from B0 (block reversal should fail)")
mu, G, A, B = bowtie(2, False)
G[3, 0] += 0.4
np.fill_diagonal(G, 0.0)
np.fill_diagonal(G, -G.sum(1))
GA, errA = partial_reverse(mu, G, A)
print("   rowsum err %.1e  law diff %.1e" % (abs(errA).max(), maxdiff(mu, G, mu, GA)))
