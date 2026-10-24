"""Exact checks of the finite-horizon theorem, Theorem `thm:finite-horizon`, and Remark `rem:finite-size`.

Part A. The reversible path 1-2-3 with q12 = 1, q21 = 2, q23 = q32 = 1 (stationary law
(1/2, 1/4, 1/4)) and the start mu = (0.5, 0.3, 0.2), with the design of Theorem
`thm:reversible-reconstruction`: R = 4 (the norm of S rounded up), b = 1, H = 2R, U = 8R/b^2 and
the suppression level M = 4R + 4UR^2. For each ordered edge (i,j) the field is v_i = H, v_j = 0
and v_k = -M.
  * The constants lambda_ij(v) and K_ij(v) of the pair are computed in two ways (the symmetric
    form and the general formula of Proposition `prop:constant`), and 1/t_ij = (q_i - H) - lambda_ij(v).
  * For N = 10^3, ..., 10^6 the exact face maxima M_{i}(v) and M_{ij}(v) of P_N(n) e^{T v.n/N}
    come from the run expansion of the killed law on the pair (Lemma `lem:runs`), maximized over
    every composition (for N > 20000 over a window around the peak of a strided scan, and the
    window is compared with the full scan at N = 10^5). The entry time tau_N solves
    M_{ij} = M_{i}, and the difference of the two logarithms is checked to increase on a grid.
    We compare tau_N with t_ij(1 - eps_N) + c_ij/L, eps_N = log L/(2L), and with the root tau0
    of the crossing equation T/t_ij + (1/2) log T = L - log(K_ij(v)/mu_i), and we check the face
    maximum formula of Proposition `prop:uniform-facemax`(b) at T = tau_N L.
  * At N = 300 a dynamic program over all compositions of the three states finds the support of
    the global maximizer of the weighted law at 0.5, 0.99, 1.01 and 1.2 times tau_N.
  * The singleton switches x_{i,N} of part (a), in closed form, against
    x_i + 2R log(mu_1/mu_i)/L, for N = 10^3, ..., 10^6.
Part B. Remark `rem:finite-size`: the two-state chain q1 = q2 = 1 of the class R = 3, b = 1, with
the uniform start and the field (2R, 0). The exact entry time of the pair at N = 10^4, ..., 10^7
(run expansion, the maximum over the compositions by a four-stage zoom whose first stage checks
unimodality, and bisection on a sign change that is checked to be unique on a grid), against
t_12 (1 - eps_N) and against the prediction t_12 (1 - eps_N) + c_12/L.

Every check is an assertion. Needs numpy and scipy. Run:  py -I verify_finite_horizon.py
(about a minute)
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


CHECKS = 0


def ok(cond, what):
    global CHECKS
    if not cond:
        raise AssertionError(what)
    CHECKS += 1
    print("  ok   ", what)


def part_a():
    print(f"Part A. ||S||_2 = {normS:.6f}, R = {R}, b = {b:.6f}, H = {H}, U = {U:.4f}, M = {Mbig:.2f}")
    pairs = [(0, 1), (1, 0), (1, 2), (2, 1)]
    for (i, j) in pairs:
        lam, K, astar = pair_constants(i, j)       # asserts that the two formulas for K agree
        t = t_limit(i, j)
        c_pred = -t * (math.log(t) + 2 * math.log(K / mu[i])) / 2
        ok(abs(1 / t - ((qv[i] - H) - lam)) < 1e-12,
           f"pair ({i+1},{j+1}): t_ij = {t:.6f}, lambda_ij(v) = {lam:.6f}, K_ij(v) = {K:.6f} (two formulas), "
           f"c_ij = {c_pred:.4f}, 1/t_ij = (q_i - H) - lambda_ij(v)")
        print("      N      tau_N     t(1-eps)   (tau_N-t(1-eps))L-c   (tau_N-tau0)L^2   face-max resid   increasing")
        devs, cross, resid_last = [], [], None
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
                assert lfull == lm and nfull == nbest
            dev = (tauN - corr) * L - c_pred
            devs.append((N, dev, math.log(L) / L))
            cross.append((tauN - tau0) * L * L)
            assert mono
            resid_last = resid
            print(f"{N:>8d}  {tauN:9.6f}  {corr:9.6f}  {dev:18.4f}  {cross[-1]:16.4f}  {resid:14.5f}   {mono}")
        ok(all(abs(dev) <= 20 * r for N, dev, r in devs[1:])
           and abs(devs[1][1]) > abs(devs[2][1]) > abs(devs[3][1]),
           f"pair ({i+1},{j+1}): |tau_N - t(1-eps_N) - c/L| <= 20 log L/L^2 for N >= 10^4 and decreasing; "
           f"window = full scan at 10^5; the difference of the log maxima increases in tau")
        ok(max(abs(x) for x in cross) < 6, f"pair ({i+1},{j+1}): |tau_N - tau0| L^2 < 6 (crossing equation)")
        ok(abs(resid_last) < 0.05, f"pair ({i+1},{j+1}): face-maximum formula off by {resid_last:.4f} in the log at N = 10^6")
    N = 300
    i, j = 0, 1
    tauN, _, _ = crossing_root(N, i, j)
    v = np.array([H, 0.0, -Mbig])
    sup = {}
    for f in (0.5, 0.99, 1.01, 1.2):
        best = full_dp_supports(N, f * tauN * math.log(N), v)
        sup[f] = max(best.items(), key=lambda kv: kv[1][0])[0]
    ok(sup[0.5] == sup[0.99] == (0,) and sup[1.01] == sup[1.2] == (0, 1),
       f"N = 300, pair (1,2), tau_N = {tauN:.6f}: the global maximizer over all compositions has support "
       f"{{1}} at 0.5 and 0.99 tau_N and {{1,2}} at 1.01 and 1.2 tau_N")
    tau0s = 1 / (2 * R)
    worst = 0.0
    for N in (10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6):
        L = math.log(N)
        T = tau0s * L
        h = T / N
        for ii in (1, 2):
            x = ((N - 1) * (math.log1p(-h * qv[0]) - math.log1p(-h * qv[ii])) + math.log(mu[0] / mu[ii])) / T
            pred = qv[ii] - qv[0] + math.log(mu[0] / mu[ii]) / T
            worst = max(worst, abs(x - pred) / (L / N))
    ok(worst <= 1, f"singleton switches: |x_iN - x_i - 2R log(mu_1/mu_i)/L| <= {worst:.3f} L/N for N = 10^3..10^6")


# ---------------------------------------------------------------- Part B: two states
def log_pair_atom(N, T, q1, q2, mu2, v, a_vals, Mmax):
    h = T / N
    a = np.asarray(a_vals, dtype=np.int64)
    bcount = N - a
    out = np.full(a.shape, -np.inf)
    l1 = math.log1p(-h * q1)
    l2 = math.log1p(-h * q2)
    Ms = np.arange(2, Mmax + 1)
    lg = lambda x: gammaln(np.maximum(x, 1))
    for start in (1, 2):
        if start == 1:
            m1, m2 = (Ms + 1) // 2, Ms // 2
            logW = math.log(mu2[0]) + m2 * math.log(q1) + (m1 - 1) * math.log(q2)
        else:
            m2, m1 = (Ms + 1) // 2, Ms // 2
            logW = math.log(mu2[1]) + m1 * math.log(q2) + (m2 - 1) * math.log(q1)
        A = a[:, None] - 1
        B = bcount[:, None] - 1
        K1 = m1[None, :] - 1
        K2 = m2[None, :] - 1
        valid = (K1 <= A) & (K2 <= B)
        with np.errstate(invalid="ignore", divide="ignore"):
            lb = lg(A + 1) - lg(K1 + 1) - lg(A - K1 + 1) + lg(B + 1) - lg(K2 + 1) - lg(B - K2 + 1)
        terms = (logW[None, :] + (Ms[None, :] - 1) * math.log(h) + lb
                 + (A + 1 - m1[None, :]) * l1 + (B + 1 - m2[None, :]) * l2)
        terms = np.where(valid, terms, -np.inf)
        mx = terms.max(axis=1)
        s = np.log(np.exp(terms - mx[:, None]).sum(axis=1)) + mx
        out = np.logaddexp(out, s)
    return out + h * (v[0] * a + v[1] * bcount)


def pair_max2(N, T, q1, q2, mu2, v):
    Mmax = int(min(N, 6 * T + 80))
    lo, hi = 1, N - 1
    for stage in range(4):
        grid = np.unique(np.clip(np.linspace(lo, hi, 400).astype(np.int64), 1, N - 1))
        vals = log_pair_atom(N, T, q1, q2, mu2, v, grid, Mmax)
        j = int(np.argmax(vals))
        if stage == 0:
            dv = np.diff(vals)
            assert np.all(dv[:j] >= -1e-9) and np.all(dv[j:] <= 1e-9), "coarse profile not unimodal"
        if hi - lo <= 400:
            return float(vals.max())
        lo = int(grid[max(j - 1, 0)])
        hi = int(grid[min(j + 1, len(grid) - 1)])
    grid = np.arange(lo, hi + 1, dtype=np.int64)
    return float(log_pair_atom(N, T, q1, q2, mu2, v, grid, Mmax).max())


def entry_time2(N, q1, q2, mu2, v, lo, hi):
    L = math.log(N)

    def gap(tau):
        T = tau * L
        h = T / N
        s1 = math.log(mu2[0]) + (N - 1) * math.log1p(-h * q1) + T * v[0]
        s2 = math.log(mu2[1]) + (N - 1) * math.log1p(-h * q2) + T * v[1]
        return pair_max2(N, T, q1, q2, mu2, v) - max(s1, s2)
    grid = np.linspace(lo, hi, 9)
    signs = [bool(gap(x) > 0) for x in grid]
    changes = [k for k in range(1, len(signs)) if signs[k] != signs[k - 1]]
    assert signs[0] is False and signs[-1] is True and len(changes) == 1
    a, bb = grid[changes[0] - 1], grid[changes[0]]
    for _ in range(24):
        m = 0.5 * (a + bb)
        if gap(m) > 0:
            bb = m
        else:
            a = m
    return 0.5 * (a + bb)


def part_b():
    R2, b2 = 3.0, 1.0
    q1 = q2 = 1.0
    v = (2 * R2, 0.0)
    mu2 = np.array([0.5, 0.5])
    pi2 = np.array([0.5, 0.5])
    sw = math.sqrt(q1 * q2)
    ev, evec = np.linalg.eigh(np.array([[q1, -sw], [-sw, q2]]) - np.diag(v))
    psi = np.abs(evec[:, 0])
    alpha = psi ** 2
    r, l = psi / np.sqrt(pi2), psi * np.sqrt(pi2)
    K = (mu2 @ r) * l.sum() / math.sqrt(4 * math.pi) * math.sqrt(psi[0] * psi[1] * sw) / (alpha[0] * alpha[1])
    t = 1.0 / ((q1 - v[0]) - ev[0])
    c = -t * (0.5 * math.log(t) + math.log(K / mu2[0]))
    print(f"Part B. q1 = q2 = 1, R = 3, b = 1, uniform start: t_12 = {t:.4f}, c_12 = {c:.4f}, K = {K:.4f}")
    rows = []
    for N in (10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7):
        L = math.log(N)
        first = t * (1 - math.log(L) / (2 * L))
        pred = first + c / L
        tN = entry_time2(N, q1, q2, mu2, v, 0.5 * t, 1.5 * t)
        rows.append((N, tN, first, pred, L * L * (tN - pred)))
        print(f"   N = {N:>8d}: t_N = {tN:.6f}, t(1-eps) = {first:.6f}, prediction {pred:.6f}, L^2 (t_N - pred) = {rows[-1][4]:.4f}")
    ok(round(t, 2) == 6.16 and round(c, 1) == -16.5, "t_12 = 6.16 and c_12 = -16.5 as in the remark")
    N, tN, first, pred, _ = rows[-1]
    ok(round(tN, 2) == 4.65 and round(first, 2) == 5.63 and round(pred, 2) == 4.60,
       f"N = 10^7: t_12,N = {tN:.2f}, t_12(1-eps_N) = {first:.2f}, prediction {pred:.2f} (remark: 4.65, 5.63, 4.60)")
    ok(max(abs(x[4]) for x in rows) < 15, "L^2 |t_N - prediction| stays below 15 for N = 10^4..10^7")


def main():
    part_a()
    part_b()
    print(f"verify_finite_horizon: all {CHECKS} checks passed")


if __name__ == "__main__":
    main()
