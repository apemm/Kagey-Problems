# check_second_moments.py
# Problem 131, Paper C2, question O1(c). Floating-point check of the
# reconstruction of G = D^{1/2} Q D^{-1/2} up to transpose from pi and the
# symmetric parts of G, G^2, G^3 (equivalently the stationary second moments of
# the occupation times). Algorithm of Theorem 4 of 01_report.md:
#   S = sym G, N = sym G^2 - S^2 = K^2, M = sym G^3 - S^3 - S N - N S = K S K;
#   the eigenplanes of N give K up to one sign per plane; the blocks P_k M P_l
#   fix the products of signs on pairs of planes coupled by S.
# Run: py -I check_second_moments.py
import numpy as np

rng = np.random.default_rng(20261025)


def stationary(Q):
    d = Q.shape[0]
    A = np.vstack([Q.T, np.ones(d)])
    b = np.zeros(d + 1); b[-1] = 1
    return np.linalg.lstsq(A, b, rcond=None)[0]


def sym(A):
    return (A + A.T) / 2


def data(Q):
    pi = stationary(Q)
    e = np.sqrt(pi)
    G = np.diag(e) @ Q @ np.diag(1 / e)
    return pi, G, [sym(np.linalg.matrix_power(G, m)) for m in (1, 2, 3)]


def reconstruct(pi, sG, tol=1e-8):
    """Return (G_hat, status). status 'ok', 'repeated', or 'disconnected'."""
    S, S2, S3 = sG
    N = S2 - S @ S
    M = S3 - S @ S @ S - S @ N - N @ S
    vals, vecs = np.linalg.eigh(N)
    order = np.argsort(vals)
    vals, vecs = vals[order], vecs[:, order]
    planes, i = [], 0
    scale = max(1.0, np.abs(vals).max())
    while i < len(vals):
        if vals[i] < -1e-12 * scale:
            gap = 1e-5 * abs(vals[i])      # pairing tolerance relative to the eigenvalue
            if i + 1 >= len(vals) or abs(vals[i + 1] - vals[i]) > gap:
                return None, "unpaired"
            if i + 2 < len(vals) and abs(vals[i + 2] - vals[i]) < gap:
                return None, "repeated"
            sig = np.sqrt(-vals[i])
            v1, v2 = vecs[:, i], vecs[:, i + 1]
            planes.append(sig * (np.outer(v2, v1) - np.outer(v1, v2)))
            i += 2
        else:
            i += 1
    r = len(planes)
    eps = [0] * r
    if r == 0:
        return S, "ok"
    eps[0] = 1
    stack, seen = [0], {0}
    proj = [-(Kk @ Kk) / (-(Kk @ Kk)).trace() * 2 for Kk in planes]
    while stack:
        k = stack.pop()
        for l in range(r):
            if l in seen:
                continue
            C = planes[k] @ S @ planes[l]
            if np.linalg.norm(C) < 1e-9 * scale ** 2:
                continue
            B = proj[k] @ M @ proj[l]
            eps[l] = eps[k] * int(np.sign(np.sum(B * C)))
            seen.add(l); stack.append(l)
    status = "ok" if len(seen) == r else "disconnected"
    K = sum(eps[k] * planes[k] for k in range(r))
    return S + K, status


def random_Q(d, sparsity=0.0):
    Q = rng.exponential(1.0, (d, d))
    Q[rng.random((d, d)) < sparsity] = 0
    perm = rng.permutation(d)          # keep a directed cycle: irreducible
    for k in range(d):
        Q[perm[k], perm[(k + 1) % d]] += rng.exponential(1.0) + 0.1
    np.fill_diagonal(Q, 0)
    np.fill_diagonal(Q, -Q.sum(1))
    return Q


def test(Q, label):
    pi, G, sG = data(Q)
    Gh, status = reconstruct(pi, sG)
    if Gh is None:
        return status, None
    err = min(np.abs(Gh - G).max(), np.abs(Gh - G.T).max())
    return status, err


for d in (3, 4, 5, 6, 7, 8):
    worst, bad = 0.0, 0
    for t in range(200):
        status, err = test(random_Q(d, sparsity=0.3 if t % 2 else 0.0), "")
        if status != "ok" or err is None or err > 1e-6:
            bad += 1
        else:
            worst = max(worst, err)
    print(f"d = {d}: 200 random Q, failures = {bad}, worst error = {worst:.2e}")

# d = 4: S and N = K^2 alone suffice (K has rank <= 2 on e-perp)
Q4 = np.array([[-4.7, 0.7, 1, 3], [1.3, -9.3, 2, 6], [2, 2, -4.4, 0.4], [1, 1, 2, -4]])
print("paper d = 4 example:", test(Q4, "Q4"))

# the d = 5 memoryless example of check_gluing_and_counterexample.py
Q5 = np.array([[0, 2, 1, 1, 2], [1, 0, 2, 1, 2], [2, 1, 0, 1, 2],
               [1, 1, 1, 0, 1], [2, 2, 2, 4, 0]], dtype=float)
np.fill_diagonal(Q5, -Q5.sum(1))
pi5, G5, sG5 = data(Q5)
N5 = sG5[1] - sG5[0] @ sG5[0]
print("d = 5 memoryless example: eigenvalues of K^2 =", np.round(np.linalg.eigvalsh(N5), 6))
print("d = 5 memoryless example:", test(Q5, "Q5"))
