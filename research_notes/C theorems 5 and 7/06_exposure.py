"""Exposure lemma checks for Theorem 4 of Paper C (route T4, file 06).

For a connected face F and a field v on F, the leading scores of the subfaces of F
are Phi(H) = |H| - 1 + tau*lambda_H(v), lambda_H = smallest real eigenvalue of
A_H - diag(v_H), A = -Q. Reducible H are scored by their best component.

(1) Singleton reference. F and {i} share a hull edge iff
    lambda_j > lambda_i for j != i in F, and
    (lambda_i - lambda_H)/(|H|-1) < (lambda_i - lambda_F)/(|F|-1) for proper H, |H| >= 2.
    We maximize the smallest margin over v (random restarts plus Nelder-Mead).
(2) Descent. At a generic v the first face to take over from F as tau decreases is the
    unique argmax over proper H of (|F|-|H|)/(lambda_H - lambda_F). We record the partner.
(3) Suppression. For G not inside F, with v = -M off F, lambda_G >= lambda_{G cap F} - eps(M).
"""
import itertools
import numpy as np
from scipy.optimize import minimize

rng = np.random.default_rng(20261024)


def lam(A, v, H):
    H = list(H)
    B = A[np.ix_(H, H)] - np.diag(v[H])
    return np.min(np.real(np.linalg.eigvals(B)))


def irreducible(Q, H):
    H = list(H)
    k = len(H)
    if k == 1:
        return True
    R = (Q[np.ix_(H, H)] > 0) | np.eye(k, dtype=bool)
    for _ in range(k):
        R = R | ((R.astype(int) @ R.astype(int)) > 0)
    return R.all()


def subsets(F):
    F = list(F)
    for r in range(1, len(F)):
        for H in itertools.combinations(F, r):
            yield H


def margin_singleton(A, Q, F, i, vF):
    v = np.zeros(A.shape[0])
    v[list(F)] = np.clip(vF, -40, 40)
    k = len(F)
    li = lam(A, v, [i])
    lF = lam(A, v, F)
    gF = (li - lF) / (k - 1)
    m = np.inf
    for H in subsets(F):
        if len(H) == 1:
            if H[0] != i:
                m = min(m, lam(A, v, H) - li)
        elif irreducible(Q, H):
            m = min(m, gF - (li - lam(A, v, H)) / (len(H) - 1))
    return m / (1.0 + abs(gF))


def best_singleton_margin(Q, F, restarts=40):
    A = -Q
    best = (-np.inf, None, None)
    k = len(F)
    for i in F:
        for _ in range(restarts):
            x0 = rng.normal(scale=3.0, size=k)
            f = lambda x: -margin_singleton(A, Q, F, i, x)
            res = minimize(f, x0, method="Nelder-Mead",
                           options={"maxiter": 1500, "xatol": 1e-9, "fatol": 1e-12})
            if -res.fun > best[0]:
                best = (-res.fun, i, res.x)
    return best


def descent_partner(Q, F, vF):
    A = -Q
    v = np.zeros(A.shape[0])
    v[list(F)] = vF
    k = len(F)
    lF = lam(A, v, F)
    ratios = []
    for H in subsets(F):
        if irreducible(Q, H):
            ratios.append(((k - len(H)) / (lam(A, v, H) - lF), H))
    ratios.sort(reverse=True)
    return ratios[0], ratios[1][0]


def gen_dense(d):
    Q = rng.uniform(0.1, 3.0, size=(d, d))
    np.fill_diagonal(Q, 0)
    np.fill_diagonal(Q, -Q.sum(1))
    return Q


def gen_sparse(d):
    while True:
        Q = np.zeros((d, d))
        perm = rng.permutation(d)
        for a in range(d):  # directed Hamiltonian cycle keeps Q irreducible
            Q[perm[a], perm[(a + 1) % d]] = rng.uniform(0.2, 3.0)
        for _ in range(rng.integers(0, d)):
            a, b = rng.choice(d, 2, replace=False)
            Q[a, b] = rng.uniform(0.2, 3.0)
        np.fill_diagonal(Q, 0)
        np.fill_diagonal(Q, -Q.sum(1))
        if irreducible(Q, range(d)):
            return Q


def gen_strong_pair(d, L=50.0):
    Q = gen_sparse(d)
    Q[0, 1] += L
    Q[1, 0] += L
    np.fill_diagonal(Q, 0)
    np.fill_diagonal(Q, -Q.sum(1))
    return Q


if __name__ == "__main__":
    print("(1) singleton reference: best margin over v (positive = F and {i} share a hull edge)")
    worst = np.inf
    count = 0
    for name, gen in [("dense", gen_dense), ("sparse", gen_sparse), ("strongpair", gen_strong_pair)]:
        for d in (3, 4):
            for trial in range(4 if d == 3 else 2):
                Q = gen(d)
                m, i, x = best_singleton_margin(Q, tuple(range(d)), restarts=6 if d == 3 else 4)
                worst = min(worst, m)
                count += 1
                print(f"  {name:10s} d={d} trial={trial} best margin={m:+.4f} reference i={i}")
    print(f"  worst best-margin over {count} generators: {worst:+.4f}")

    # A fixed hard case: strong pair {0,1}, state 2 joined by a one-way loop 1->2->0.
    Q = np.zeros((3, 3)); Q[0, 1] = Q[1, 0] = 50.0; Q[1, 2] = 1.0; Q[2, 0] = 1.0
    np.fill_diagonal(Q, -Q.sum(1))
    m, i, x = best_singleton_margin(Q, (0, 1, 2), restarts=10)
    print(f"  strong pair with one-way loop: margin={m:+.4f}, i={i}, v={np.round(x,3)}")

    print("(2) descent partner at random fields (all faces F = V)")
    for name, gen in [("dense", gen_dense), ("sparse", gen_sparse)]:
        for d in (3, 4, 5):
            Q = gen(d)
            for _ in range(3):
                vF = rng.normal(scale=2.0, size=d)
                (r1, H), r2 = descent_partner(Q, tuple(range(d)), vF)
                print(f"  {name:6s} d={d} partner={H} tau_1={r1:.4f} next ratio={r2:.4f} gap={r1-r2:.2e}")

    print("(3) suppression: max over G not in F of lambda_{G cap F} - lambda_G, F={0,1,2}, d=5")
    Q = gen_dense(5); A = -Q; F = [0, 1, 2]
    for M in (10.0, 100.0, 1000.0):
        worst = -np.inf; low = np.inf
        for _ in range(20):
            v = -M * np.ones(5); v[F] = rng.uniform(-3, 3, size=3)
            for r in range(1, 6):
                for G in itertools.combinations(range(5), r):
                    if set(G) <= set(F):
                        continue
                    P = [g for g in G if g in F]
                    lG = lam(A, v, G)
                    if P:
                        worst = max(worst, lam(A, v, P) - lG)
                    else:
                        low = min(low, lG)
        print(f"  M={M:7.1f}: max (lambda_P - lambda_G) over G meeting F = {worst:.3e};"
              f" min lambda_G over G outside F = {low:.1f}")
