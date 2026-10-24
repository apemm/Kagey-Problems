"""Exact check of the finite-N pair-entry time in the protected design (Paper C, Theorem 5a).

Three-state reversible path 1-2-3 with q12=1, q21=2, q23=1, q32=1 (stationary law (1/2,1/4,1/4)),
start mu=(0.5,0.3,0.2).  For a retained edge (i,j) the field is v_i=H, v_j=0, v_k=-M.
For each N we compute, from the exact run expansion of the two-state killed law, the exact
face maxima M_{i}(v) and M_{ij}(v) of the controlled atom P_N(n) exp(T v.n/N), and solve
M_{ij} = M_{i} for tau = T/log N.  We compare with
    t_ij (1 - log log N / (2 log N))
and with the root tau0 of the crossing equation  T/t_ij + (1/2) log T = L - log(K_ij(v)/mu_i).
At N=300 a full dynamic program over all compositions checks that the exact global
maximizer has support {i} just below the computed entry time and {i,j} just above it.

Run:  py -I 01_pair_entry_check.py
"""
import math
import functools
print = functools.partial(print, flush=True)
import numpy as np
from scipy.special import gammaln
from scipy.optimize import brentq

np.seterr(divide="ignore")

Q = np.array([[-1.0, 1.0, 0.0],
              [2.0, -3.0, 1.0],
              [0.0, 1.0, -1.0]])
mu = np.array([0.5, 0.3, 0.2])
d = 3
qv = -np.diag(Q)
pi = np.array([0.5, 0.25, 0.25])
assert np.allclose(pi @ Q, 0)
for a in range(d):
    for c in range(d):
        assert abs(pi[a] * Q[a, c] - pi[c] * Q[c, a]) < 1e-14
Dh = np.diag(np.sqrt(pi))
S = Dh @ (-Q) @ np.linalg.inv(Dh)
S = (S + S.T) / 2
normS = np.linalg.norm(S, 2)
R = math.ceil(normS * 10) / 10          # a known bound ||S||_2 <= R
edges = [(a, c) for a in range(d) for c in range(a + 1, d) if Q[a, c] > 0]
b = min(math.sqrt(Q[a, c] * Q[c, a]) for a, c in edges)
H = 2 * R
U = 8 * R / b ** 2
Mbig = 4 * R + 4 * U * R ** 2


def t_limit(i, j):
    w = Q[i, j] * Q[j, i]
    Delta = qv[i] - qv[j]          # d_i - d_j (d is q shifted by q_1)
    return (math.sqrt((H - Delta) ** 2 + 4 * w) + H - Delta) / (2 * w)


def pair_constants(i, j):
    """lambda_ij(v), K_ij(v) for v_F = (H, 0), two independent ways."""
    w = Q[i, j] * Q[j, i]
    SF = np.array([[qv[i] - H, -math.sqrt(w)], [-math.sqrt(w), qv[j]]])
    ev, evec = np.linalg.eigh(SF)
    lam = ev[0]
    phi = np.abs(evec[:, 0])
    pis = np.array([pi[i], pi[j]])
    mus = np.array([mu[i], mu[j]])
    K1 = (np.sum(mus * phi / np.sqrt(pis)) * np.sum(phi * np.sqrt(pis)) * w ** 0.25
          / (math.sqrt(4 * math.pi) * (phi[0] * phi[1]) ** 1.5))
    # general formula: Perron vectors of Q_F + diag v, tilted generator, det Sigma = 2ab/(a+b)^3
    B = np.array([[-qv[i] + H, Q[i, j]], [Q[j, i], -qv[j]]])
    evr, Vr = np.linalg.eig(B)
    k = np.argmax(evr.real)
    assert abs(evr[k].real + lam) < 1e-10
    r = np.abs(Vr[:, k].real)
    evl, Vl = np.linalg.eig(B.T)
    k2 = np.argmax(evl.real)
    l = np.abs(Vl[:, k2].real)
    l = l / (l @ r)
    a_ = Q[i, j] * r[1] / r[0]
    b_ = Q[j, i] * r[0] / r[1]
    detSig = 2 * a_ * b_ / (a_ + b_) ** 3
    K2 = (mus @ r) * (l.sum()) / (math.sqrt(2 * math.pi) * math.sqrt(detSig))
    assert abs(K1 / K2 - 1) < 1e-10, (K1, K2)
    return lam, K1, l * r


class PairLaw:
    """Exact log P_N(n) on the face {i,j} (killed two-state run expansion)."""

    def __init__(self, N, i, j):
        self.N, self.i, self.j = N, i, j
        self.ni = np.arange(1, N)
        self.nj = N - self.ni
        self.G = gammaln(np.arange(N + 2) + 1.0)   # G[k] = log k!

    def logbinom(self, n, k):
        # log C(n, k) for arrays n >= 0 and scalar k, -inf where k > n
        out = np.full(n.shape, -np.inf)
        ok = k <= n
        out[ok] = self.G[n[ok]] - self.G[k] - self.G[n[ok] - k]
        return out

    def logP(self, T, idx=None, rmax=4000):
        N, i, j = self.N, self.i, self.j
        h = T / N
        la = math.log1p(-h * qv[i])
        lc = math.log1p(-h * qv[j])
        lh = math.log(h)
        lqij, lqji = math.log(Q[i, j]), math.log(Q[j, i])
        ni, nj = (self.ni, self.nj) if idx is None else (self.ni[idx], self.nj[idx])
        acc = np.full(ni.shape, -np.inf)
        small = 0
        for r in range(1, rmax):
            lw_rr = np.logaddexp(math.log(mu[i]) + r * lqij + (r - 1) * lqji,
                                 math.log(mu[j]) + r * lqji + (r - 1) * lqij)
            lw_x = r * (lqij + lqji)
            best = -np.inf
            for (mi, mj, lw) in ((r, r, lw_rr), (r + 1, r, math.log(mu[i]) + lw_x),
                                 (r, r + 1, math.log(mu[j]) + lw_x)):
                t = (lw + (mi + mj - 1) * lh + self.logbinom(ni - 1, mi - 1)
                     + self.logbinom(nj - 1, mj - 1) + (ni - mi) * la + (nj - mj) * lc)
                best = max(best, np.max(t - np.where(np.isfinite(acc), acc, t)))
                acc = np.logaddexp(acc, t)
            if r > 5 and best < -60:
                small += 1
                if small > 3:
                    break
            else:
                small = 0
        return acc


def log_single(N, T, i, vi):
    h = T / N
    return math.log(mu[i]) + (N - 1) * math.log1p(-h * qv[i]) + T * vi


def log_pair_max(law, T, vi, vj, full=False):
    # exact maximum over n; for large N a strided scan locates the peak and the maximum is then
    # taken over every composition in a window around it (full=True scans every composition)
    h = T / law.N
    N = law.N
    if full or N <= 20000:
        idx = np.arange(N - 1)
    else:
        stride = N // 4000
        coarse = np.arange(0, N - 1, stride)
        lc = law.logP(T, coarse) + h * (vi * law.ni[coarse] + vj * law.nj[coarse])
        k0 = int(coarse[np.argmax(lc)])
        idx = np.arange(max(0, k0 - 3 * stride), min(N - 1, k0 + 3 * stride + 1))
    lp = law.logP(T, idx)
    lw = lp + h * (vi * law.ni[idx] + vj * law.nj[idx])
    k = int(np.argmax(lw))
    return lw[k], law.ni[idx][k]


def crossing_root(N, i, j):
    law = PairLaw(N, i, j)
    L = math.log(N)
    t = t_limit(i, j)
    D = lambda tau: log_pair_max(law, tau * L, H, 0.0)[0] - log_single(N, tau * L, i, H)
    lo, hi = 1 / (4 * R), 1.2 * t
    # stay inside the stochastic range h q_max <= 1/2
    hi = min(hi, 0.5 * N / (qv.max() * L))
    assert D(lo) < 0 < D(hi), (D(lo), D(hi))
    tau = brentq(D, lo, hi, xtol=1e-13, rtol=1e-13)
    # monotonicity of D on a grid around the root (convexity argument predicts increase)
    grid = np.linspace(lo, hi, 7)
    vals = [D(x) for x in grid]
    mono = all(vals[k] < vals[k + 1] for k in range(len(vals) - 1))
    return tau, mono, law


def tau_crossing_eq(N, i, j, K):
    L = math.log(N)
    t = t_limit(i, j)
    kappa = math.log(K / mu[i])
    f = lambda T: T / t + 0.5 * math.log(T) - (L - kappa)
    T0 = brentq(f, 1e-6, 10 * t * L)
    return T0 / L


def full_dp_supports(N, T, v):
    """Exact max of log P_N(n) + h v.n by support, over all compositions (3 states)."""
    h = T / N
    P = np.eye(d) + h * Q
    lP = np.log(P)
    A = [np.full((N + 1, N + 1), -np.inf) for _ in range(d)]
    A[0][1, 0] = math.log(mu[0])
    A[1][0, 1] = math.log(mu[1])
    A[2][0, 0] = math.log(mu[2])
    for _ in range(1, N):
        new = []
        for s2 in range(d):
            stack = np.stack([A[s] + lP[s, s2] for s in range(d)])
            m = np.max(stack, axis=0)
            fin = np.isfinite(m)
            val = np.full(m.shape, -np.inf)
            val[fin] = m[fin] + np.log(np.sum(np.exp(stack[:, fin] - m[fin]), axis=0))
            sh = np.full(m.shape, -np.inf)
            if s2 == 0:
                sh[1:, :] = val[:-1, :]
            elif s2 == 1:
                sh[:, 1:] = val[:, :-1]
            else:
                sh = val
            new.append(sh)
        A = new
    tot = A[0]
    for s in range(1, d):
        tot = np.logaddexp(tot, A[s])
    n1, n2 = np.meshgrid(np.arange(N + 1), np.arange(N + 1), indexing="ij")
    n3 = N - n1 - n2
    valid = n3 >= 0
    lw = np.where(valid, tot + h * (v[0] * n1 + v[1] * n2 + v[2] * np.where(valid, n3, 0)), -np.inf)
    best = {}
    for a in range(N + 1):
        for c in range(N + 1 - a):
            e = N - a - c
            supp = tuple(k for k, x in enumerate((a, c, e)) if x > 0)
            if lw[a, c] > best.get(supp, (-np.inf,))[0]:
                best[supp] = (lw[a, c], (a, c, e))
    return best


def main():
    print(f"||S||_2 = {normS:.6f}, R = {R}, b = {b:.6f}, H = {H}, U = {U:.4f}, M = {Mbig:.2f}")
    pairs = [(0, 1), (1, 0), (1, 2), (2, 1)]
    for (i, j) in pairs:
        lam, K, astar = pair_constants(i, j)
        t = t_limit(i, j)
        assert abs(1 / t - ((qv[i] - H) - lam)) < 1e-12
        c_pred = -t * (math.log(t) + 2 * math.log(K / mu[i])) / 2
        print()
        print(f"retained pair (i,j) = ({i+1},{j+1}): t_ij = {t:.6f}, lambda_ij(v) = {lam:.6f}, "
              f"K_ij(v) = {K:.6f}, alpha*(v) = ({astar[0]:.4f},{astar[1]:.4f}), "
              f"predicted c_ij = {c_pred:.4f}")
        print("   N      tau_N(exact)  t(1-llN/2lN)  (tau_N-t(1-..))*L  tau0(cross.eq)  "
              "(tau_N-tau0)*L^2  pair-law resid  D increasing")
        for N in (10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6):
            L = math.log(N)
            tauN, mono, law = crossing_root(N, i, j)
            corr = t * (1 - math.log(L) / (2 * L))
            tau0 = tau_crossing_eq(N, i, j, K)
            T = tauN * L
            lm, nbest = log_pair_max(law, T, H, 0.0)
            resid = lm - (-L + 0.5 * math.log(T) + math.log(K) - T * lam)
            if N == 10 ** 5:
                lfull, nfull = log_pair_max(law, T, H, 0.0, full=True)
                print(f"   (window check at N=1e5: full scan minus window = {lfull - lm:.2e}, "
                      f"argmax n_i {nfull} vs {nbest})")
            print(f"{N:>8d}  {tauN:12.6f}  {corr:12.6f}  {(tauN - corr) * L:16.4f}  "
                  f"{tau0:13.6f}  {(tauN - tau0) * L * L:15.4f}  {resid:13.5f}   {mono}")
    # full dynamic program at N = 300 for the pair (1,2): global winner just below/above entry
    N = 300
    i, j = 0, 1
    tauN, _, _ = crossing_root(N, i, j)
    v = np.array([H, 0.0, -Mbig])
    print()
    print(f"full DP over all compositions, N = {N}, pair (1,2), exact entry tau_N = {tauN:.6f}")
    for tau in (0.99 * tauN, 1.01 * tauN, 0.5 * tauN, 1.2 * tauN):
        best = full_dp_supports(N, tau * math.log(N), v)
        ranked = sorted(best.items(), key=lambda kv: -kv[1][0])
        top = ranked[0]
        second = ranked[1]
        print(f"  tau = {tau:.5f}: winner support {tuple(s+1 for s in top[0])} at n = {top[1][1]}, "
              f"runner-up {tuple(s+1 for s in second[0])}, log ratio {top[1][0]-second[1][0]:.4f}")
    # singleton switch: exact formula vs x_i + log(mu_1/mu_i)/(tau0 L)
    print()
    print("singleton switch x_{i,N} at tau0 = 1/(2R) (exact closed form)")
    tau0s = 1 / (2 * R)
    for N in (10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6):
        L = math.log(N)
        T = tau0s * L
        h = T / N
        row = []
        for ii in (1, 2):
            x = ((N - 1) * (math.log1p(-h * qv[0]) - math.log1p(-h * qv[ii])) + math.log(mu[0] / mu[ii])) / T
            xi = qv[ii] - qv[0]
            row.append((x, xi + math.log(mu[0] / mu[ii]) / T))
        print(f"  N = {N:>8d}: x_2N = {row[0][0]:.6f} (pred {row[0][1]:.6f}),  "
              f"x_3N = {row[1][0]:.6f} (pred {row[1][1]:.6f})")


if __name__ == "__main__":
    main()
