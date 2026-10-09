"""More S2 checks: module reversal on four states, the pair decoder, discrete time."""
import itertools
import numpy as np
from scipy.linalg import expm

rng = np.random.default_rng(11)


def phi(mu, G, lam, t=1.0):
    return mu @ expm(t * (G - np.diag(lam))) @ np.ones(len(G))


def maxdiff(mu, G1, G2, trials=60, t=1.0):
    d = len(G1)
    w = 0.0
    for _ in range(trials):
        lam = rng.uniform(0, 3, d)
        a, b = phi(mu, G1, lam, t), phi(mu, G2, lam, t)
        w = max(w, abs(a - b) / abs(a))
    return w


def fix_diag(G):
    G = G.copy()
    np.fill_diagonal(G, 0.0)
    np.fill_diagonal(G, -G.sum(1))
    return G


def stat(G):
    d = len(G)
    A = np.vstack([G.T, np.ones(d)])
    b = np.zeros(d + 1)
    b[-1] = 1
    return np.linalg.lstsq(A, b, rcond=None)[0]


print("1. module reversal, d = 4, every rate positive, start not stationary")
# outside states 0,1 ; module {2,3} lumped to b
Lg = fix_diag(np.array([[0, 0.9, 0.5], [0.3, 0, 1.1], [0.8, 0.4, 0]]))  # lumped chain on {0,1,b}
mub = stat(Lg)
nu = np.array([0.35, 0.65])
G = np.zeros((4, 4))
G[0, 1], G[1, 0] = Lg[0, 1], Lg[1, 0]
for x in (0, 1):
    G[x, 2], G[x, 3] = Lg[x, 2] * nu
    G[2, x] = G[3, x] = Lg[2, x]
G[2, 3], G[3, 2] = 1.7, 0.2  # inside the module, not balanced against nu
G = fix_diag(G)
mu = np.array([mub[0], mub[1], mub[2] * nu[0], mub[2] * nu[1]])
Lr = (Lg.T * mub[None, :]) / mub[:, None]  # reversed lumped chain
G2 = np.zeros((4, 4))
G2[0, 1], G2[1, 0] = Lr[0, 1], Lr[1, 0]
for x in (0, 1):
    G2[x, 2], G2[x, 3] = Lr[x, 2] * nu
    G2[2, x] = G2[3, x] = Lr[2, x]
G2[2, 3], G2[3, 2] = G[2, 3], G[3, 2]
G2 = fix_diag(G2)
print("   min off-diagonal rate %.3f, |mu G| = %.3f (not stationary)" % (
    min(G[i, j] for i in range(4) for j in range(4) if i != j), abs(mu @ G).max()))
print("   |G - G'| = %.3f" % abs(G - G2).max())
for t in (1.0, 0.3, 4.0):
    print("   horizon %.1f: law difference %.1e" % (t, maxdiff(mu, G, G2, t=t)))
print("   G  =\n", np.round(G, 4))
print("   G' =\n", np.round(G2, 4))
print("   mu =", np.round(mu, 4))


def decode(mu, q, a, c, tol=1e-9):
    """All generators with the given start law, exit rates, round-trip products a_ij and
    two-way flows c_ij: choose which root is which on every pair, keep the exit rates."""
    d = len(mu)
    pairs = [(i, j) for i in range(d) for j in range(i + 1, d)]
    disc = {p: max(c[p] ** 2 - 4 * mu[p[0]] * mu[p[1]] * a[p], 0.0) ** 0.5 for p in pairs}
    sols = []
    for signs in itertools.product((1, -1), repeat=len(pairs)):
        f = np.zeros((d, d))
        for p, s in zip(pairs, signs):
            i, j = p
            f[i, j] = (c[p] + s * disc[p]) / 2
            f[j, i] = (c[p] - s * disc[p]) / 2
        if np.allclose(f.sum(1), mu * q, atol=tol):
            Gc = fix_diag(f / mu[:, None])
            if not any(np.allclose(Gc, S, atol=1e-7) for S in sols):
                sols.append(Gc)
    return sols


def pair_data(mu, G):
    d = len(G)
    a, c = {}, {}
    for i in range(d):
        for j in range(i + 1, d):
            a[(i, j)] = G[i, j] * G[j, i]
            c[(i, j)] = mu[i] * G[i, j] + mu[j] * G[j, i]
    return -np.diag(G), a, c


print("2. decoder from (mu, exit rates, a_ij, c_ij)")
for d in (3, 4, 5):
    Gt = fix_diag(rng.uniform(0.3, 2.0, (d, d)))
    m = rng.dirichlet(np.ones(d) * 3)
    q, a, c = pair_data(m, Gt)
    s = decode(m, q, a, c)
    print("   d=%d generic start: %d solution(s), recovers G: %s" % (
        d, len(s), any(np.allclose(x, Gt) for x in s)))
    pi = stat(Gt)
    q, a, c = pair_data(pi, Gt)
    s = decode(pi, q, a, c)
    print("   d=%d stationary start: %d solution(s)" % (d, len(s)))
q, a, c = pair_data(mu, G)
s = decode(mu, q, a, c)
print("   d=4 module example: %d pair-level solutions; G' among them: %s" % (
    len(s), any(np.allclose(x, G2) for x in s)))

print("3. discrete time: rank of P -> law of K_N, known start, d = 3")


def law(P, mu, N):
    d = 3
    A = np.zeros((N + 1, N + 1, d), dtype=complex)
    A[1, 0, 0], A[0, 1, 1], A[0, 0, 2] = mu
    for _ in range(N - 1):
        B = np.zeros_like(A)
        fl = A @ P
        B[1:, :, 0] += fl[:-1, :, 0]
        B[:, 1:, 1] += fl[:, :-1, 1]
        B[:, :, 2] += fl[:, :, 2]
        A = B
    return A.sum(2).ravel()


offs = [(i, j) for i in range(3) for j in range(3) if i != j]
P0 = rng.dirichlet(np.ones(3) * 2, 3)
m3 = np.array([0.5, 0.3, 0.2])
for N in (2, 3, 4, 5):
    J = []
    for (i, j) in offs:
        Pc = P0.astype(complex)
        Pc[i, j] += 1e-30j
        Pc[i, i] -= 1e-30j
        J.append(law(Pc, m3, N).imag / 1e-30)
    sv = np.linalg.svd(np.array(J).T, compute_uv=False)
    print("   N=%d rank %d of 6" % (N, int((sv > 1e-9 * sv[0]).sum())))
