"""Fisher information in the count vector K_N versus the full path, d = 3.

Chain: N steps, P = I + (T/N) Q, start law mu (known) or the stationary law of Q.
Derivatives by the complex-step method, so they are exact to rounding.
"""
import sys
import numpy as np
from scipy.linalg import eigh

d = 3
OFFS = [(i, j) for i in range(d) for j in range(d) if i != j]


def build_Q(theta):
    Q = np.zeros((d, d), dtype=complex)
    for (i, j), t in zip(OFFS, theta):
        Q[i, j] = t
    Q[np.arange(d), np.arange(d)] = -Q.sum(1)
    return Q


def stat(Q):
    A = np.vstack([Q.T[:-1], np.ones(d)])
    b = np.zeros(d, dtype=complex)
    b[-1] = 1
    return np.linalg.solve(A, b)


def count_law(theta, T, N, mu_mode, mu_fixed=None):
    """Law of (K_1, K_2) (K_3 = N - K_1 - K_2), complex-valued for complex theta."""
    Q = build_Q(theta)
    P = np.eye(d) + (T / N) * Q
    mu = stat(Q) if mu_mode == "stationary" else mu_fixed.astype(complex)
    A = np.zeros((N + 1, N + 1, d), dtype=complex)
    A[1, 0, 0] = mu[0]
    A[0, 1, 1] = mu[1]
    A[0, 0, 2] = mu[2]
    for _ in range(N - 1):
        B = np.zeros_like(A)
        flow = A @ P  # flow[..., j] = sum_i A[..., i] P[i, j]
        B[1:, :, 0] += flow[:-1, :, 0]
        B[:, 1:, 1] += flow[:, :-1, 1]
        B[:, :, 2] += flow[:, :, 2]
        A = B
    return A.sum(2)


def fisher_counts(theta, T, N, mu_mode, mu_fixed=None, h=1e-30):
    p0 = count_law(theta, T, N, mu_mode, mu_fixed).real
    grads = []
    for k in range(len(theta)):
        th = np.array(theta, dtype=complex)
        th[k] += 1j * h
        grads.append(count_law(th, T, N, mu_mode, mu_fixed).imag / h)
    mask = p0 > 1e-300
    I = np.zeros((len(theta), len(theta)))
    for a in range(len(theta)):
        for b in range(a, len(theta)):
            I[a, b] = I[b, a] = (grads[a][mask] * grads[b][mask] / p0[mask]).sum()
    return I


def fisher_path(theta, T, N, mu_mode, mu_fixed=None, h=1e-30):
    Q = build_Q(theta).real
    P = np.eye(d) + (T / N) * Q
    mu = stat(build_Q(theta)).real if mu_mode == "stationary" else mu_fixed
    occ = np.zeros(d)
    m = mu.copy()
    for _ in range(N - 1):
        occ += m
        m = m @ P
    n = len(theta)
    I = np.zeros((n, n))
    # transitions: dP[i,j]/dtheta_k
    for i in range(d):
        for j in range(d):
            g = np.zeros(n)
            for k, (a, b) in enumerate(OFFS):
                if a == i and b == j:
                    g[k] = T / N
                if a == i and i == j:
                    g[k] = -T / N
            I += occ[i] * np.outer(g, g) / P[i, j]
    if mu_mode == "stationary":
        dmu = np.zeros((n, d))
        for k in range(n):
            th = np.array(theta, dtype=complex)
            th[k] += 1j * h
            dmu[k] = stat(build_Q(th)).imag / h
        for i in range(d):
            I += np.outer(dmu[:, i], dmu[:, i]) / mu[i]
    return I


def efficiencies(IK, IF):
    w = eigh(IK, IF, eigvals_only=True)
    return np.sort(w)[::-1]


if __name__ == "__main__":
    rng = np.random.default_rng(3)
    theta = np.array([1.0, 0.4, 0.7, 1.3, 0.5, 0.9])  # Q01 Q02 Q10 Q12 Q20 Q21
    mu = np.array([0.5, 0.3, 0.2])
    Q = build_Q(theta).real

    print("A. known start, small T: eigenvalues of I_K / T (three stay O(1), three go like T)")
    for T in (0.4, 0.2, 0.1, 0.05):
        IK = fisher_counts(theta, T, 240, "known", mu)
        ev = np.sort(np.linalg.eigvalsh(IK))[::-1]
        print("   T=%.2f  eig/T: %s" % (T, np.array2string(ev / T, precision=4)))

    print("B. efficiencies (generalized eigenvalues of I_K against the full path)")
    for T in (0.05, 0.2, 1.0, 5.0, 20.0):
        N = 240 if T <= 5 else 400
        IK = fisher_counts(theta, T, N, "known", mu)
        IF = fisher_path(theta, T, N, "known", mu)
        print("   known      T=%5.2f  %s" % (T, np.array2string(efficiencies(IK, IF), precision=3)))
    for T in (0.05, 0.2, 1.0, 5.0, 20.0):
        N = 240 if T <= 5 else 400
        IK = fisher_counts(theta, T, N, "stationary")
        IF = fisher_path(theta, T, N, "stationary")
        print("   stationary T=%5.2f  %s" % (T, np.array2string(efficiencies(IK, IF), precision=3)))

    print("C. first order: I_K ~ T * sum grad(c_ij) grad(c_ij)^T / c_ij")
    A = np.zeros((6, 6))
    for i in range(d):
        for j in range(i + 1, d):
            g = np.zeros(6)
            g[OFFS.index((i, j))] = mu[i]
            g[OFFS.index((j, i))] = mu[j]
            c = mu[i] * Q[i, j] + mu[j] * Q[j, i]
            A += np.outer(g, g) / c
    for T in (0.1, 0.05, 0.025):
        IK = fisher_counts(theta, T, 400, "known", mu)
        print("   T=%.3f  max|I_K/T - A| = %.4f" % (T, abs(IK / T - A).max()))

    print("D. second order on ker A: v^T I_K v / T^2 -> sum mu_i (dq_i)^2 + (dtau)^2/(2 tau)")
    f = mu[:, None] * Q
    np.fill_diagonal(f, 0)
    cc = f + f.T
    JJ = f - f.T
    tau = 0.0
    for y in range(d):
        x, z = [k for k in range(d) if k != y]
        tau += (cc[x, y] * cc[y, z] + JJ[x, y] * JJ[y, z]) / (2 * mu[y])
    # directions: delta f_ij = +e/2, delta f_ji = -e/2 on one pair (changes J_ij by e, keeps c)
    for (i, j) in ((0, 1), (1, 2), (0, 2)):
        v = np.zeros(6)
        v[OFFS.index((i, j))] = 0.5 / mu[i]
        v[OFFS.index((j, i))] = -0.5 / mu[j]
        dq = np.zeros(d)
        dq[i] = 0.5 / mu[i]
        dq[j] = -0.5 / mu[j]
        k = [s for s in range(d) if s not in (i, j)][0]
        # d tau / d J_ij = (J_jk/mu_j + J_ki/mu_i) / 2
        dtau = (JJ[j, k] / mu[j] + JJ[k, i] / mu[i]) / 2
        pred = (mu * dq * dq).sum() + dtau ** 2 / (2 * tau)
        out = []
        for T in (0.08, 0.04, 0.02):
            IK = fisher_counts(theta, T, 400, "known", mu)
            out.append(v @ IK @ v / T ** 2)
        print("   pair %s: T=.08,.04,.02 -> %s   predicted %.4f" % (
            (i, j), np.array2string(np.array(out), precision=4), pred))

    print("E. stationary start at a reversible chain: one zero eigenvalue at every T")
    pi = np.array([0.5, 0.3, 0.2])
    S = np.array([[0, .30, .12], [.30, 0, .21], [.12, .21, 0]])
    Qr = S / pi[:, None]
    th_r = np.array([Qr[i, j] for i, j in OFFS])
    for T in (0.5, 2.0, 8.0):
        IK = fisher_counts(th_r, T, 240, "stationary")
        ev = np.sort(np.linalg.eigvalsh(IK))
        print("   T=%.1f  smallest two eig: %.2e %.2e" % (T, ev[0], ev[1]))
    print("   non-reversible stationary chain, circulation j: info in the j direction ~ j^2")
    for eps in (0.08, 0.04, 0.02):
        fl = S.copy()
        fl[0, 1] += eps / 2; fl[1, 0] -= eps / 2
        fl[1, 2] += eps / 2; fl[2, 1] -= eps / 2
        fl[2, 0] += eps / 2; fl[0, 2] -= eps / 2
        Qe = fl / pi[:, None]
        th_e = np.array([Qe[i, j] for i, j in OFFS])
        IK = fisher_counts(th_e, 2.0, 240, "stationary")
        ev = np.sort(np.linalg.eigvalsh(IK))
        print("   j=%.2f  smallest eig %.3e   ratio to j^2: %.4f" % (eps, ev[0], ev[0] / eps ** 2))

    if "--curve" in sys.argv:
        Ts = np.geomspace(0.02, 40, 34)
        rows = []
        for T in Ts:
            N = int(max(160, 14 * T))
            ek = efficiencies(fisher_counts(theta, T, N, "known", mu), fisher_path(theta, T, N, "known", mu))
            es = efficiencies(fisher_counts(theta, T, N, "stationary"), fisher_path(theta, T, N, "stationary"))
            rows.append(np.concatenate([[T], ek, es]))
            print("   curve T=%.3f done" % T, flush=True)
        np.savetxt("s2_efficiency_curve.csv", np.array(rows), delimiter=",",
                   header="T,known1..6,stationary1..6")
