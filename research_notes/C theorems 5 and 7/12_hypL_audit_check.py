"""Independent numerical check for the audit 12_hypL_audit_complex_route.md.

Written from the statement of Hypothesis L (paperC/sec_boundary.tex at 0ffc041) and Lemma
lem:layer-exact, without importing anything from the 09_ or 10_ scripts.

Run from any folder:  py -I 12_hypL_audit_check.py > 12_hypL_audit_check_output.txt

Exact side. f^(z)_G(s) = e^{-<d(z), s>} H_z(s), H_z(s) = sum_m W_z(m) prod_j s_j^{m_j-1}/(m_j-1)!,
W_z(m) = sum over words w in G with no equal neighbours and counts m of
mu^(z)_{w_1} prod A(z)_{w_l w_{l+1}} e^(z)_{w_M}. Computed by a dynamic program over the word
length, for any number g of letters (the array holds the counts of the first g-1 letters).
The same program run with |A(z)|, |mu^(z)|, |e^(z)| gives the sum of the moduli of the terms
(an upper bound for it), hence the cancellation exponent kappa.

Predicted side. The torus phase Phi_z(z') = beta_1 g_z(z') + sum_{j>=2} beta_j z_j, its critical
point zeta'(beta, z) continued from the real tilt at z = 0 along the segment [0, z], the matrix
J = Z_c grad^2 Phi_z Z_c, and
    pred = S^{-(g-1)/2} (2 pi)^{-(g-1)/2} det(J)^{-1/2} b_z(zeta') prod zeta_j e^{-S(<d(z),beta> - Phi_z(zeta'))},
with the branch of det(J)^{-1/2} continued from the positive root.

Cross-checks. For real z >= 0 the constant is also computed from Definition def:tilt applied to
A(z), mu^(z), e^(z) (the Sigma formula of Section sec:layer-setting). For g = 2 the word sum is
compared with the Bessel closed form of Lemma lem:L-two.

Needs numpy and scipy (scipy only for the Bessel functions of the g = 2 check).
"""
import time
from math import pi

import numpy as np
from numpy.linalg import det, eigvalsh, inv, solve


def facet(Q, mu, i):
    n = Q.shape[0]
    G = [j for j in range(n) if j != i]
    QG = Q[np.ix_(G, G)]
    A = QG.copy()
    np.fill_diagonal(A, 0.0)
    return dict(A=A, q=-np.diag(QG), cm=Q[G, i].copy(), cp=Q[i, G].copy(), muG=mu[G].copy(),
                mui=mu[i], g=len(G))


def weights(fd, z):
    A = (fd['A'] + z * np.outer(fd['cm'], fd['cp'])).astype(complex)
    np.fill_diagonal(A, 0.0)
    d = (fd['q'] - z * fd['cm'] * fd['cp']).astype(complex)
    mu = (fd['muG'] + z * fd['mui'] * fd['cp']).astype(complex)
    e = (1.0 + z * fd['cm']).astype(complex)
    return A, d, mu, e


# ------------------------------------------------------------------ exact word sum
def word_sum(A, mu, e, s, Lmax=4000, tol=1e-22):
    """Returns (H, Habs, L) with H the word sum and Habs the same sum for |A|, |mu|, |e|."""
    g = len(s)
    out = []
    for AA, mm, ee in [(A, mu, e), (np.abs(A), np.abs(mu), np.abs(e))]:
        out.append(_word_sum_one(AA.astype(complex), mm.astype(complex), ee.astype(complex), s,
                                 Lmax, tol, g))
    (H, L1), (Ha, L2) = out
    return H, Ha.real, max(L1, L2)


def _word_sum_one(A, mu, e, s, Lmax, tol, g):
    """Dynamic program over the word length. N[a][c_0, ..., c_{g-2}] is the weighted sum of the
    words of the current length L that end in letter a and have c_j letters j (j < g-1), the last
    letter having L - sum c letters, with the factors s_j^{m_j-1}/(m_j-1)! folded in."""
    d = g - 1
    cap = 48

    def grow(N, cap, newcap):
        M = [np.zeros((newcap,) * d, complex) for _ in range(g)]
        if N is not None:
            sl = (slice(0, cap),) * d
            for a in range(g):
                M[a][sl] = N[a]
        return M

    N = grow(None, 0, cap)
    for a in range(g):
        idx = [0] * d
        if a < d:
            idx[a] = 1
        N[a][tuple(idx)] = mu[a]
    gsum = np.indices((cap,) * d).sum(axis=0)
    allpos = np.all(np.indices((cap,) * d) >= 1, axis=0)
    logscale = 0.0
    total = []
    best = -np.inf
    quiet = 0
    for L in range(1, Lmax + 1):
        w = min(L + 2, cap)
        sl = (slice(0, w),) * d
        last = L - gsum[sl]
        valid = allpos[sl] & (last >= 1)
        contrib = sum(e[a] * N[a][sl][valid].sum() for a in range(g))
        total.append((contrib, logscale))
        size = np.log(abs(contrib)) + logscale if contrib != 0 else -np.inf
        if size > best:
            best, quiet = size, 0
        elif size < best + np.log(tol) and L > 5:
            quiet += 1
            if quiet >= 30:
                break
        if L + 4 >= cap:
            newcap = cap + 48
            N = grow(N, cap, newcap)
            cap = newcap
            gsum = np.indices((cap,) * d).sum(axis=0)
            allpos = np.all(np.indices((cap,) * d) >= 1, axis=0)
        w2 = L + 3
        sl2 = (slice(0, w2),) * d
        lastnew = (L + 1) - gsum[sl2]
        acc = [None] * g
        for a in range(g):
            t = np.zeros((w2,) * d, complex)
            for b in range(g):
                if b != a:
                    t += A[b, a] * N[b][sl2]
            acc[a] = t
        newN = [np.zeros((cap,) * d, complex) for _ in range(g)]
        for a in range(g):
            if a < d:
                cnt = np.arange(w2)
                fac = np.where(cnt >= 2, s[a] / np.maximum(cnt - 1, 1), 1.0)
                shape = [1] * d
                shape[a] = w2
                fac = fac.reshape(shape)
                shifted = np.zeros((w2,) * d, complex)
                src = [slice(None)] * d
                dst = [slice(None)] * d
                src[a] = slice(0, w2 - 1)
                dst[a] = slice(1, w2)
                shifted[tuple(dst)] = acc[a][tuple(src)]
                newN[a][sl2] = shifted * fac
            else:
                fac = np.where(lastnew >= 2, s[a] / np.maximum(lastnew - 1, 1), 1.0)
                fac = np.where(lastnew >= 1, fac, 0.0)
                newN[a][sl2] = acc[a] * fac
        mx = max(np.abs(x[sl2]).max() for x in newN)
        if mx > 1e150:
            for x in newN:
                x /= mx
            logscale += np.log(mx)
        N = newN
    ref = max(ls for _, ls in total)
    val = sum(c * np.exp(ls - ref) for c, ls in total)
    return val * np.exp(ref), L


# ------------------------------------------------------------------ torus side
def torus_parts(A, mu, e, zp):
    a1, b1, Ap = A[0, 1:], A[1:, 0], A[1:, 1:]
    X = inv(np.diag(zp) - Ap)
    u = a1 @ X
    v = X @ b1
    gval = u @ b1
    grad = -u * v
    M = u[:, None] * X * v[None, :]
    hess = M + M.T
    bval = (mu[0] + mu[1:] @ v) * (e[0] + u @ e[1:])
    return gval, grad, hess, bval


def real_tilt(A, beta, iters=200):
    """Minimizer r of u -> sum_{i != j} beta_i A_ij u_j / u_i (Newton in log u, first entry fixed)."""
    g = len(beta)
    psi = np.zeros(g)
    for _ in range(iters):
        E = np.exp(psi[None, :] - psi[:, None])
        W = beta[:, None] * A * E
        grad = W.sum(axis=0) - W.sum(axis=1)
        Hm = np.diag(W.sum(axis=0) + W.sum(axis=1)) - W - W.T
        step = np.zeros(g)
        step[1:] = solve(Hm[1:, 1:], grad[1:])
        psi -= step
        if np.abs(step).max() < 1e-15:
            break
    r = np.exp(psi)
    return r, (A @ r) / r


def crit(A, mu, e, beta, zp0, iters=60):
    zp = np.array(zp0, complex)
    for _ in range(iters):
        gval, grad, hess, bval = torus_parts(A, mu, e, zp)
        F = beta[0] * grad + beta[1:]
        step = solve(beta[0] * hess, -F)
        zp = zp + step
        if np.abs(step).max() < 1e-14:
            break
    gval, grad, hess, bval = torus_parts(A, mu, e, zp)
    J = np.diag(zp) @ (beta[0] * hess) @ np.diag(zp)
    Phi = beta[0] * gval + beta[1:] @ zp
    return zp, Phi, J, bval


def prediction_data(fd, beta, z, steps=40):
    """Continue the critical point and the branch of det(J)^{1/2} from z = 0 to z."""
    A0, _, _, _ = weights(fd, 0.0)
    r0, th0 = real_tilt(A0.real, beta)
    zp = th0[1:].astype(complex)
    sq = None
    mins = []
    for t in np.linspace(0, 1, steps + 1):
        A, d, mu, e = weights(fd, t * z)
        zp, Phi, J, bval = crit(A, mu, e, beta, zp)
        root = np.sqrt(det(J))
        if sq is not None and abs(root - sq) > abs(root + sq):
            root = -root
        sq = root
        mins.append(eigvalsh(J.real).min())
    A, d, mu, e = weights(fd, z)
    m = fd['g'] - 1
    logC = np.log((2 * pi) ** (-m / 2) * bval * np.prod(zp) / sq)
    Jrate = np.sum(beta * d) - Phi
    return dict(zp=zp, J=J, Jrate=Jrate, logC=logC, minReJ=min(mins), th0=th0)


def C_def_tilt(fd, beta, z):
    """Constant of Section sec:layer-setting for real z >= 0, from Definition def:tilt."""
    A, d, mu, e = weights(fd, z)
    A = A.real
    r, th = real_tilt(A, beta)
    l = beta / r
    g = len(beta)
    R = np.diag(r)
    Qh = inv(R) @ (A - np.diag(th)) @ R
    one = np.ones(g)
    Zm = inv(np.outer(one, beta) - Qh) - np.outer(one, beta)
    Gam = np.diag(beta) @ Zm + Zm.T @ np.diag(beta)
    Sig = Gam[1:, 1:]
    C = (mu.real @ r) * (l @ e.real) / ((2 * pi) ** ((g - 1) / 2) * np.sqrt(det(Sig)))
    Jr = np.sum(beta * (d.real - th))
    return C, Jr


# ------------------------------------------------------------------ runs
def run(name, Q, mu, i, beta, zlist, Slist):
    fd = facet(Q, mu, i)
    beta = np.asarray(beta, float)
    g = fd['g']
    print("=" * 96)
    print(f"{name}: |G| = {g}, i = {i}, beta = {beta}")
    print("Q =")
    print(Q)
    print(f"mu = {mu}, c^- = {fd['cm']}, c^+ = {fd['cp']}")
    # fold / Re J scan on the negative real axis and on a few rays
    print("scan: least eigenvalue of Re J along rays z = rho e^{i ang} (continuation in 40 steps)")
    for ang in [0, 0.5, 0.75, 1.0, 1.25, 1.5]:
        row = []
        for rho in [0.02, 0.05, 0.1, 0.15, 0.2]:
            try:
                pdz = prediction_data(fd, beta, rho * np.exp(1j * pi * ang))
                row.append(f"{pdz['minReJ']:8.4f}")
            except Exception:
                row.append("    fail")
        print(f"   ang = {ang:4.2f} pi, rho = 0.02 .. 0.2: " + " ".join(row))
    for z in [0.0, 0.05, 0.1]:
        pdz = prediction_data(fd, beta, z)
        Cd, Jd = C_def_tilt(fd, beta, z)
        print(f"real z = {z}: C_torus = {np.exp(pdz['logC']).real:.12f}, C_def_tilt = {Cd:.12f}, "
              f"J_torus = {pdz['Jrate'].real:.12f}, J_def_tilt = {Jd:.12f}")
    print(f"{'z':>22} " + " ".join(f"{S:>17.1f}" for S in Slist))
    for z in zlist:
        pdz = prediction_data(fd, beta, z)
        A, d, muz, ez = weights(fd, z)
        cells = []
        prev = None
        ratios = []
        for S in Slist:
            s = S * beta
            H, Ha, L = word_sum(A, muz, ez, s)
            kappa = np.log(Ha) - np.log(abs(H))
            logpred = -S * pdz['Jrate'] + pdz['logC'] - ((g - 1) / 2) * np.log(S)
            eps = np.exp(np.log(H) - np.sum(d * s) - logpred) - 1
            flag = '*' if 1e-15 * np.exp(kappa) > 0.02 * abs(eps) else ' '
            cells.append(f"{S * abs(eps):9.5f}{flag}(k{kappa:4.1f})")
            if prev is not None:
                ratios.append(S * abs(eps) / prev)
            prev = S * abs(eps)
        print(f"{str(np.round(z, 4)):>22} " + " ".join(cells))
        print(f"{'ratios':>22} " + " ".join(f"{x:17.4f}" for x in ratios)
              + f"   minReJ on [0,z] = {pdz['minReJ']:.4f}")


def two_state_check():
    from scipy.special import iv
    print("=" * 96)
    print("g = 2: word sum against the Bessel form of lem:L-two and against the torus prediction")
    Q = np.array([[-2.3, 1.2, 1.1], [0.7, -1.6, 0.9], [1.5, 0.4, -1.9]])
    mu = np.array([0.3, 0.3, 0.4])
    fd = facet(Q, mu, 2)
    beta = np.array([0.6, 0.4])
    for z in [0.0, 0.1j, 0.15 * np.exp(2j)]:
        A, d, p, e = weights(fd, z)
        for S in [3.0, 12.0]:
            s = S * beta
            H, Ha, L = word_sum(A, p, e, s)
            tau = A[0, 1] * A[1, 0]
            xi = 2 * np.sqrt(tau * s[0] * s[1])
            Hb = (p[0] * e[0] * np.sqrt(tau * s[0] / s[1]) + p[1] * e[1] * np.sqrt(tau * s[1] / s[0])) * iv(1, xi) \
                + (p[0] * A[0, 1] * e[1] + p[1] * A[1, 0] * e[0]) * iv(0, xi)
            pdz = prediction_data(fd, beta, z)
            U = p[0] * e[0] * np.sqrt(tau * beta[0] / beta[1]) + p[1] * e[1] * np.sqrt(tau * beta[1] / beta[0])
            V = p[0] * A[0, 1] * e[1] + p[1] * A[1, 0] * e[0]
            CL = (U + V) / (np.sqrt(4 * pi) * (tau * beta[0] * beta[1]) ** 0.25)
            print(f"   z = {np.round(z, 4)}, S = {S}: |H_words/H_Bessel - 1| = {abs(H / Hb - 1):.2e}, "
                  f"|C_torus/C_L-two - 1| = {abs(np.exp(pdz['logC']) / CL - 1):.2e}")


def main():
    t0 = time.time()
    print("numpy", np.__version__)
    two_state_check()

    # |G| = 3: a new non-reversible face with four states, start mass on i, c^- and c^+ with zeros
    Q3 = np.array([[0.0, 1.8, 0.3, 0.0],
                   [0.6, 0.0, 1.4, 1.5],
                   [1.9, 0.2, 0.0, 0.7],
                   [1.1, 0.0, 0.4, 0.0]])
    np.fill_diagonal(Q3, -Q3.sum(axis=1))
    mu3 = np.array([0.15, 0.25, 0.2, 0.4])
    run("Face with four states (|G| = 3)", Q3, mu3, 3, [0.25, 0.45, 0.30],
        [0.0, 0.08, -0.08, 0.08j, 0.1 * np.exp(2j * pi / 3), 0.12 * np.exp(-1j * pi / 4)],
        [5.0, 10.0, 20.0, 40.0, 80.0])

    # |G| = 4: a facet with four states, face with five states
    Q4 = np.array([[0.0, 1.5, 0.7, 0.5, 0.8],
                   [0.5, 0.0, 1.5, 0.0, 0.0],
                   [0.0, 0.5, 0.0, 1.5, 1.2],
                   [1.5, 0.0, 0.5, 0.0, 0.3],
                   [0.5, 1.0, 0.0, 0.9, 0.0]])
    np.fill_diagonal(Q4, -Q4.sum(axis=1))
    mu4 = np.array([0.2, 0.1, 0.3, 0.15, 0.25])
    run("Facet with four states (|G| = 4)", Q4, mu4, 4, [0.3, 0.25, 0.2, 0.25],
        [0.0, 0.08, -0.08, 0.08j, 0.1 * np.exp(2j * pi / 3)],
        [4.0, 8.0, 16.0, 32.0])
    print(f"total time {time.time() - t0:.0f} s")


if __name__ == "__main__":
    main()
