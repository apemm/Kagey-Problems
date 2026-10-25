"""Numerical check of Hypothesis L (paperC/sec_boundary.tex, hyp:L) for faces with four states.

Companion of 09_hypL_complex_laplace.md. Run from this folder with

    py -I 09_hypL_check.py > 09_hypL_check_output.txt

Setting. F = {0,1,2,3}, i = 3, G = {0,1,2}, so |G| = 3 and m = |G| - 1 = 2 circles in the torus
representation. For complex z the weighted chain has off-diagonal part A(z) = A_G + z offdiag(c^- c^+T),
diagonal d(z) = q_G - z c^- o c^+, start mu^(z) = mu_G + z mu_i c^+ and end vector e^(z) = 1 + z c^-.

Exact quantity. f^(z)_G(S beta) = e^{-<d(z), S beta>} H_z(S beta), where
H_z(s) = sum_m W_z(m) prod_j s_j^{m_j - 1}/(m_j - 1)! is the word sum of Lemma lem:layer-exact.
It is computed by a dynamic program over the word length (function log_H_words). The weights
s_j^{m_j-1}/(m_j-1)! are folded into the recursion and the layers are rescaled, so any S is fine.

Prediction. S^{-1} C_G(beta, z) e^{-S J_G(beta, z)}, where J_G and C_G are the holomorphic continuations of
the rate and the local-law constant, computed from the complex tilt (the complex critical point of
psi -> Psi_beta(e^psi) - z P_beta(e^psi), Newton's method continued from z = 0 along the segment
[0, z] in 25 steps), Definition def:tilt with A(z), mu^(z), e^(z), and the branch of sqrt(det Sigma)
continued along the same segment from the positive root.

Accuracy of the word sum. For complex z the terms of the word sum cancel: their moduli add up to the
value of the dominating nonnegative system, which is larger than |H_z| by the factor e^kappa with
kappa proportional to S. The script reports kappa; cells where 1e-15 e^kappa is not small against
|eps| are marked * and there the torus identity of Lemma 3.1 (which has no cancellation on the
torus through the critical point) is used as the exact value. Where both are accurate they agree
to 1e-15.

Cross-checks. (a) The complex critical point of the torus phase z' -> beta_1 g_z(z') + sum beta_j z_j
equals theta'(beta, z) from the complex tilt, g_z(theta') = theta_1, and the torus amplitude
(2 pi)^{-m/2} det(J)^{-1/2} b_z(theta') prod theta_j equals C_G(beta, z) (Lemma D of the note).
(b) The 2-torus integral of Lemma C at the radii |theta'(beta, z)|, rotated by arg theta'(beta, z),
reproduces H_z(S beta) from the word sum (trapezoidal rule, exponentially accurate).
(c) The least eigenvalue of Re J(beta, z) along circles |z| = const (hypothesis (ii) of Lemma B).
(d) The word dynamic program against a direct enumeration of W(m) at small S.

Needs numpy only.
"""
import sys
import time
from math import pi

import numpy as np
from numpy.linalg import LinAlgError, det, eigvalsh, inv, solve

np.set_printoptions(precision=6, linewidth=120)


# ----------------------------------------------------------------------------- the two chains
def chain_cycle4():
    """Non-reversible 4-cycle: q_{j,j+1} = 2, q_{j+1,j} = 1 (mod 4). Uniform start."""
    Q = np.zeros((4, 4))
    for j in range(4):
        Q[j, (j + 1) % 4] = 2.0
        Q[(j + 1) % 4, j] = 1.0
    np.fill_diagonal(Q, -Q.sum(axis=1))
    mu = np.full(4, 0.25)
    return Q, mu


def chain_k4():
    """Complete graph on four states with non-reversible rates and a non-uniform start."""
    off = np.array([[0.0, 1.0, 2.0, 0.5],
                    [1.5, 0.0, 1.0, 2.0],
                    [0.5, 2.0, 0.0, 1.0],
                    [2.0, 0.5, 1.5, 0.0]])
    Q = off.copy()
    np.fill_diagonal(Q, -off.sum(axis=1))
    mu = np.array([0.1, 0.2, 0.3, 0.4])
    return Q, mu


def kolmogorov_defect(Q):
    """max over 3-cycles of |log(prod forward) - log(prod backward)|; 0 for reversible Q."""
    d = Q.shape[0]
    worst = 0.0
    for a in range(d):
        for b in range(d):
            for c in range(d):
                if len({a, b, c}) == 3:
                    f = Q[a, b] * Q[b, c] * Q[c, a]
                    r = Q[a, c] * Q[c, b] * Q[b, a]
                    if f > 0 and r > 0:
                        worst = max(worst, abs(np.log(f / r)))
    return worst


def facet_data(Q, mu, G, i):
    G = list(G)
    QG = Q[np.ix_(G, G)]
    A = QG.copy()
    np.fill_diagonal(A, 0.0)
    return dict(A=A, q=-np.diag(QG), cm=Q[G, i].copy(), cp=Q[i, G].copy(),
                muG=mu[G].copy(), mui=mu[i], g=len(G))


def weights(fd, z):
    """A(z), d(z), mu^(z), e^(z) for complex z."""
    A = fd['A'] + z * np.outer(fd['cm'], fd['cp'])
    A = A.astype(complex)
    np.fill_diagonal(A, 0.0)
    d = fd['q'] - z * fd['cm'] * fd['cp']
    mu = fd['muG'] + z * fd['mui'] * fd['cp']
    e = 1.0 + z * fd['cm']
    return A, d.astype(complex), mu.astype(complex), e.astype(complex)


# ----------------------------------------------------------------------------- the complex tilt
def complex_tilt(A, beta, psi0=None, iters=200):
    """Critical point of psi -> sum_{j != j'} beta_j A_jj' e^{psi_j' - psi_j} (complex Newton, psi_0 = 0).

    Returns r = e^psi, l = beta / r, theta = A r / r. For real nonnegative A this is the tilt of
    Definition def:tilt (the minimizer of the concave dual), and for complex A its holomorphic
    continuation when started from the real solution.
    """
    g = len(beta)
    psi = np.zeros(g, complex) if psi0 is None else np.array(psi0, complex)
    for _ in range(iters):
        if not np.all(np.isfinite(psi)):
            break
        E = np.exp(psi[None, :] - psi[:, None])
        W = beta[:, None] * A * E
        grad = W.sum(axis=0) - W.sum(axis=1)
        Cm = W + W.T
        H = np.diag(Cm.sum(axis=1)) - Cm
        H[0, :] = 0.0
        H[:, 0] = 0.0
        H[0, 0] = 1.0
        grad = grad.copy()
        grad[0] = 0.0
        try:
            step = solve(H, grad)
        except LinAlgError:
            psi[:] = np.nan
            break
        psi = psi - step
        if np.max(np.abs(step)) < 1e-15:
            break
    r = np.exp(psi)
    l = beta / r
    theta = (A @ r) / r
    return r, l, theta, psi


def rate_and_constant_at(fd, beta, z, psi0, sqrt_prev):
    """J_G(beta, z), C_G(beta, z), theta(beta, z), psi, det Sigma at one z, warm-started from psi0.
    The square root of det Sigma is the root closest to sqrt_prev (continuation of the branch)."""
    A, d, mu, e = weights(fd, z)
    r, l, theta, psi = complex_tilt(A, beta, psi0)
    g = fd['g']
    m = g - 1
    J = np.sum(beta * (d - theta))
    R = np.diag(r)
    Qhat = inv(R) @ (A - np.diag(theta)) @ R
    ones = np.ones(g)
    Zm = inv(np.outer(ones, beta) - Qhat) - np.outer(ones, beta)
    D = np.diag(beta)
    Gam = D @ Zm + Zm.T @ D
    Sig = Gam[1:, 1:]
    dS = det(Sig)
    sq = np.sqrt(dS)
    if sqrt_prev is not None and abs(sq - sqrt_prev) > abs(-sq - sqrt_prev):
        sq = -sq
    C = (mu @ r) * (l @ e) / ((2 * pi) ** (m / 2) * sq)
    return dict(J=J, C=C, theta=theta, psi=psi, detSigma=dS, sqrtdet=sq, r=r, l=l)


def rate_and_constant(fd, beta, z, steps=25):
    """Holomorphic continuation of the tilt data from z = 0 to z along the segment, in `steps` steps.

    Each step warm-starts Newton's method at the previous critical point and continues the branch
    of sqrt(det Sigma). A plain Newton start from the real tilt can jump to another critical point
    when |z| is not small (this happened for the 4-cycle at z = -0.1 in a first run).
    """
    rc = rate_and_constant_at(fd, beta, 0.0, None, None)
    psi = rc['psi']
    sq = rc['sqrtdet']
    for t in np.linspace(0, 1, steps + 1)[1:]:
        rc = rate_and_constant_at(fd, beta, t * z, psi, sq)
        psi = rc['psi']
        sq = rc['sqrtdet']
    return rc


# ----------------------------------------------------------------------------- torus side (g = 3)
def torus_funcs(A, mu, e, zp):
    """g_z(z'), its gradient and Hessian in z', and b_z(z') for g = 3, z' in C^2."""
    a1 = A[0, 1:]
    b1 = A[1:, 0]
    Ap = A[1:, 1:]
    X = inv(np.diag(zp) - Ap)
    u = a1 @ X
    v = X @ b1
    gval = u @ b1
    grad = -u * v
    M = u[:, None] * X * v[None, :]
    hess = M + M.T
    bval = (mu[0] + mu[1:] @ v) * (e[0] + u @ e[1:])
    return gval, grad, hess, bval


def torus_critical_point(A, mu, e, beta, zp0, iters=100):
    zp = np.array(zp0, complex)
    for _ in range(iters):
        if not np.all(np.isfinite(zp)):
            break
        gval, grad, hess, _ = torus_funcs(A, mu, e, zp)
        F = beta[0] * grad + beta[1:]
        try:
            step = solve(beta[0] * hess, -F)
        except LinAlgError:
            zp[:] = np.nan
            break
        zp = zp + step
        if np.max(np.abs(step)) < 1e-15:
            break
    gval, grad, hess, bval = torus_funcs(A, mu, e, zp)
    Zc = np.diag(zp)
    Jmat = Zc @ (beta[0] * hess) @ Zc        # J = -Hessian in phi at the critical point
    Phi = beta[0] * gval + beta[1:] @ zp
    return zp, Phi, Jmat, bval, gval


def torus_integral_log(A, mu, e, beta, S, zc, n=512):
    """log of (2 pi)^{-2} int e^{S Phi_z(z')} b_z(z') z_2 z_3 dphi on the torus through zc (z' = zc e^{i phi})."""
    a1 = A[0, 1:]
    b1 = A[1:, 0]
    a = A[1, 2]
    b = A[2, 1]
    phi = 2 * pi * (np.arange(n) + 0.5) / n
    Z2 = zc[0] * np.exp(1j * phi)[:, None]
    Z3 = zc[1] * np.exp(1j * phi)[None, :]
    detM = Z2 * Z3 - a * b
    X11 = Z3 / detM
    X12 = a / detM
    X21 = b / detM
    X22 = Z2 / detM
    u1 = a1[0] * X11 + a1[1] * X21
    u2 = a1[0] * X12 + a1[1] * X22
    v1 = X11 * b1[0] + X12 * b1[1]
    v2 = X21 * b1[0] + X22 * b1[1]
    gval = u1 * b1[0] + u2 * b1[1]
    bval = (mu[0] + mu[1] * v1 + mu[2] * v2) * (e[0] + u1 * e[1] + u2 * e[2])
    Phi = beta[0] * gval + beta[1] * Z2 + beta[2] * Z3
    _, Phic, _, _, _ = torus_critical_point(A, mu, e, beta, zc)
    vals = np.exp(S * (Phi - Phic)) * bval * Z2 * Z3
    mean = vals.mean()
    return S * Phic + np.log(mean)


# ----------------------------------------------------------------------------- the word sum (g = 3)
def log_H_words(A, mu, e, s, Lcap, tol=1e-18, tail=40):
    """log H_z(s) for three letters by a dynamic program over the word length.

    State at length L: N[a][m1, m2] = sum over words of length L with letter counts (m1, m2, L-m1-m2)
    ending in letter a of mu_{c_1} prod A_{c_l c_{l+1}} prod_j s_j^{m_j-1}/(m_j-1)!.
    Appending letter a to a word with m_a letters a multiplies by s_a/m_a if m_a >= 1 (0 -> 1 gives 1).
    H = sum_L sum_a sum_{m1,m2>=1, m3>=1} N[a][m1,m2] e_a.
    Returns log H, the last length used, and the cancellation exponent
    kappa = log(sum of the moduli of all terms) - log |H|. The terms are summed in double precision,
    so the relative rounding error of H is of order 1e-16 e^kappa. For complex z the moduli sum to
    the value of the dominating nonnegative system, which is exponentially larger than |H_z|, so
    kappa grows linearly in S and the word sum loses its accuracy at large S. The table flags
    these cells, and the torus identity (Lemma 3.1 of the note) gives a second exact evaluation.
    """
    n = Lcap + 3
    N = [np.zeros((n, n), complex) for _ in range(3)]
    N[0][1, 0] = mu[0]
    N[1][0, 1] = mu[1]
    N[2][0, 0] = mu[2]
    idx = np.arange(n)
    I1 = idx[:, None]
    I2 = idx[None, :]
    # multiplier for the NEW count k of a letter: 1 if k == 1 else s/(k-1)
    def fac(sj):
        f = np.ones(2 * n, complex)
        k = np.arange(2, 2 * n)
        f[2:] = sj / (k - 1)
        return f
    f0, f1, f2 = fac(s[0]), fac(s[1]), fac(s[2])
    logscale = 0.0
    pieces = []      # (complex contribution, logscale)
    abspieces = []   # (sum of moduli of the terms, logscale)
    absmax = 0.0
    below = 0
    for L in range(1, Lcap + 1):
        # contribution of length L
        m3 = L - I1 - I2
        valid = (I1 >= 1) & (I2 >= 1) & (m3 >= 1)
        tot = 0j
        atot = 0.0
        for a in range(3):
            blk = N[a][:L + 1, :L + 1]
            vv = valid[:L + 1, :L + 1]
            tot += e[a] * blk[vv].sum()
            atot += abs(e[a]) * np.abs(blk[vv]).sum()
        pieces.append((tot, logscale))
        abspieces.append((atot, logscale))
        # stopping rule on the absolute layer mass, in a common scale
        val = np.log(atot) + logscale if atot > 0 else -np.inf
        if val > absmax:
            absmax = val
            below = 0
        elif val < absmax + np.log(tol):
            below += 1
            if below >= tail:
                break
        # transition L -> L+1
        Lp = L + 1
        newN = [np.zeros((Lp + 2, Lp + 2), complex) for _ in range(3)]
        m3new = Lp - I1[:Lp + 2] - I2[:, :Lp + 2]
        m3new = np.where(m3new >= 1, m3new, 1)
        F2 = f2[m3new]
        for a in range(3):
            for b in range(3):
                if a == b:
                    continue
                src = N[b][:L + 2, :L + 2]
                if a == 0:
                    # m1 -> m1 + 1
                    newN[0][1:L + 3, :L + 2] += A[b, 0] * src * f0[1:L + 3][:, None]
                elif a == 1:
                    newN[1][:L + 2, 1:L + 3] += A[b, 1] * src * f1[1:L + 3][None, :]
                else:
                    newN[2][:L + 2, :L + 2] += A[b, 2] * src * F2[:L + 2, :L + 2]
        # rescale
        mx = max(np.abs(x).max() for x in newN)
        if mx > 1e100:
            for x in newN:
                x /= mx
            logscale += np.log(mx)
        N = [np.zeros((n, n), complex) for _ in range(3)]
        for a in range(3):
            N[a][:Lp + 2, :Lp + 2] = newN[a]
    else:
        print("   warning: Lcap reached without convergence", file=sys.stderr)
    ref = max(ls for _, ls in pieces)
    total = sum(c * np.exp(ls - ref) for c, ls in pieces)
    abstotal = sum(a * np.exp(ls - ref) for a, ls in abspieces)
    logH = np.log(total) + ref
    kappa = float(np.log(abstotal) + ref - logH.real)
    return logH, L, kappa


def log_H_enum(A, mu, e, s, Lmax):
    """Independent evaluation of H at small s: W(m) by a 3-D transfer recursion, then the explicit sum."""
    from math import factorial
    n = Lmax + 2
    # T[a][m1,m2,m3] = weighted count of words with counts m ending in a
    T = np.zeros((3, n, n, n), complex)
    T[0, 1, 0, 0] = mu[0]
    T[1, 0, 1, 0] = mu[1]
    T[2, 0, 0, 1] = mu[2]
    for L in range(1, Lmax):
        for m1 in range(L + 1):
            for m2 in range(L + 1 - m1):
                m3 = L - m1 - m2
                for b in range(3):
                    w = T[b, m1, m2, m3]
                    if w == 0:
                        continue
                    for a in range(3):
                        if a == b:
                            continue
                        mm = [m1, m2, m3]
                        mm[a] += 1
                        T[a, mm[0], mm[1], mm[2]] += w * A[b, a]
    H = 0j
    for m1 in range(1, n):
        for m2 in range(1, n - m1):
            for m3 in range(1, n - m1 - m2):
                W = sum(T[a, m1, m2, m3] * e[a] for a in range(3))
                H += W * s[0] ** (m1 - 1) / factorial(m1 - 1) * s[1] ** (m2 - 1) / factorial(m2 - 1) \
                    * s[2] ** (m3 - 1) / factorial(m3 - 1)
    return np.log(H)


# ----------------------------------------------------------------------------- the checks
def run_chain(name, Q, mu, beta, zlist, Slist, torus_n=512):
    G = [0, 1, 2]
    i = 3
    fd = facet_data(Q, mu, G, i)
    beta = np.asarray(beta, float)
    print("=" * 100)
    print(f"{name}: Q =")
    print(Q)
    print(f"mu = {mu}, i = {i}, G = {G}, beta = {beta}, Kolmogorov defect = {kolmogorov_defect(Q):.4f}")
    print(f"c^- = {fd['cm']}, c^+ = {fd['cp']}")
    base = rate_and_constant(fd, beta, 0.0)
    th0 = base['theta'].real
    print(f"z = 0: theta(beta) = {th0}, J_G(beta) = {base['J'].real:.10f}, C_G(beta) = {base['C'].real:.10f}, "
          f"det Sigma = {base['detSigma'].real:.6e}")
    omega = (fd['cm'] @ base['l'].real) * (fd['cp'] @ base['r'].real)
    print(f"omega_beta = (c^- . l)(c^+ . r) = {omega:.6f}")

    # (c) real part of the Hessian along circles
    print("\n(c) least eigenvalue of Re J(beta, z) = Re[Z_c H_z(zeta') Z_c], and |det J|, on circles |z| = rho")
    print("    (J(beta,0) is real positive definite; Lemma B needs Re J >= sigma_min I on the disc used)")
    A0, d0, mu0, e0 = weights(fd, 0.0)
    J0 = torus_critical_point(A0, mu0, e0, beta, th0[1:])[2].real
    print(f"    at z = 0: J(beta,0) = {np.round(J0, 6).tolist()}, lambda_min = {eigvalsh(J0).min():.6f}")
    print("    radius of the continued critical point by direction: the first rho (step 0.005, up to 1) along")
    print("    z = rho e^{i ang} at which Re J(beta, z) stops being positive definite, or the continuation folds")
    print("    (singular Hessian or a jump of theta by more than 0.5 in one step); '>1' if neither happens.")
    line = []
    for ang in np.linspace(0, 2 * pi, 16, endpoint=False):
        rc = rate_and_constant_at(fd, beta, 0.0, None, None)
        psi, sq, prev = rc['psi'], rc['sqrtdet'], rc['theta']
        found = '>1'
        for k in range(1, 201):
            z = 0.005 * k * np.exp(1j * ang)
            rc = rate_and_constant_at(fd, beta, z, psi, sq)
            if not np.all(np.isfinite(rc['theta'])) or np.abs(rc['theta'] - prev).max() > 0.5:
                found = f"{0.005 * k:.3f}f"
                break
            psi, sq, prev = rc['psi'], rc['sqrtdet'], rc['theta']
            A, d, muz, ez = weights(fd, z)
            zp, Phi, Jm, bval, gval = torus_critical_point(A, muz, ez, beta, rc['theta'][1:])
            if not np.all(np.isfinite(zp)) or eigvalsh(Jm.real).min() <= 0:
                found = f"{0.005 * k:.3f}"
                break
        line.append(f"{ang / pi:.3f}pi:{found}")
    print("    " + "  ".join(line[:8]))
    print("    " + "  ".join(line[8:]))
    print("    (a trailing f marks a fold of the continuation; a bare number marks loss of Re J > 0)")
    for rho in [0.05, 0.1, 0.15, 0.2, 0.3, 0.4, 0.6, 0.8]:
        mins = []
        angs = np.linspace(0, 2 * pi, 24, endpoint=False)
        for ang in angs:
            z = rho * np.exp(1j * ang)
            A, d, muz, ez = weights(fd, z)
            rc = rate_and_constant(fd, beta, z)
            zp, Phi, Jm, bval, gval = torus_critical_point(A, muz, ez, beta, rc['theta'][1:])
            if np.all(np.isfinite(zp)):
                mins.append(eigvalsh(Jm.real).min())
            else:
                mins.append(-np.inf)
        k = int(np.argmin(mins))
        print(f"    rho = {rho:4.2f}: min over 24 angles of lambda_min(Re J) = {min(mins): .6f} at arg z = {angs[k]/pi:.3f} pi")

    # (a) identification of the two critical points and the two constants
    print("\n(a) complex tilt against the torus critical point, at each z used below")
    header = f"{'z':>22} {'|zeta - theta_dual|':>20} {'|g_z(theta)-theta_1|':>20} {'|C_torus/C_alg - 1|':>20} {'|detJ b1^2/(prod th^2 detSig) - 1|':>36}"
    print(header)
    for z in zlist:
        A, d, muz, ez = weights(fd, z)
        rc = rate_and_constant(fd, beta, z)
        th = rc['theta']
        zp, Phi, Jm, bval, gval = torus_critical_point(A, muz, ez, beta, th[1:])
        Ctor = (2 * pi) ** (-1) * det(Jm) ** (-0.5) * bval * np.prod(zp)
        # branch: det(J)^(-1/2) continued from the positive root; the principal root is right while
        # det J stays near the positive axis, which the printout below documents
        rel_det = det(Jm) * beta[0] ** 2 / (np.prod(th[1:]) ** 2 * rc['detSigma']) - 1
        print(f"{str(np.round(z, 4)):>22} {np.abs(zp - th[1:]).max():20.3e} {abs(gval - th[0]):20.3e} "
              f"{abs(Ctor / rc['C'] - 1):20.3e} {abs(rel_det):36.3e}")
        print(f"{'':>22}  theta(beta,z) = {np.round(th, 6)}  J_G = {np.round(rc['J'], 8)}  C_G = {np.round(rc['C'], 8)}  det J = {np.round(det(Jm), 6)}")

    # (b) and the main table
    print("\n(b) word sum (dynamic program) against the 2-torus integral through the complex critical point,")
    print("    and the main table: eps = f^(z)_G(S beta) / [S^{-1} C_G(beta,z) e^{-S J_G(beta,z)}] - 1")
    print("    kappa = log(sum of moduli of the word terms) - log|H_z|; the word sum has rounding error ~ 1e-16 e^kappa.")
    print("    A cell is marked * when 1e-15 e^kappa > 0.02 |eps|; there the word sum is not accurate enough and")
    print("    eps_t, from the exact torus identity (Lemma 3.1), is the reliable value. Unmarked cells agree.")
    print(f"{'z':>22} {'S':>6} {'L':>5} {'kappa':>7} {'|Hw/Ht-1|':>11} {'Re eps_w':>11} {'Im eps_w':>11} {'S|eps_w|':>9} {'':>1} {'Re eps_t':>11} {'Im eps_t':>11} {'S|eps_t|':>9} {'t/s':>5}")
    results = {}
    results_t = {}
    flags = {}
    for z in zlist:
        A, d, muz, ez = weights(fd, z)
        rc = rate_and_constant(fd, beta, z)
        th = rc['theta']
        thdom = rate_and_constant(fd, beta, abs(z))['theta'].real
        for S in Slist:
            s = S * beta
            t0 = time.time()
            Lcap = int(3.0 * S * float(np.sum(beta * thdom)) + 12 * np.sqrt(S * float(np.sum(beta * thdom))) + 80)
            logH, Lused, kappa = log_H_words(A, muz, ez, s, Lcap)
            logHt = torus_integral_log(A, muz, ez, beta, S, th[1:], n=torus_n)
            logpred = -S * rc['J'] + np.log(rc['C']) - 1.0 * np.log(S)
            eps = np.exp(logH - np.sum(d * s) - logpred) - 1
            eps_t = np.exp(logHt - np.sum(d * s) - logpred) - 1
            dt = time.time() - t0
            flag = '*' if 1e-15 * np.exp(kappa) > 0.02 * abs(eps_t) else ' '
            results[(z, S)] = eps
            results_t[(z, S)] = eps_t
            flags[(z, S)] = flag
            print(f"{str(np.round(z, 4)):>22} {S:6.1f} {Lused:5d} {kappa:7.2f} {abs(np.exp(logH - logHt) - 1):11.2e} "
                  f"{eps.real:11.3e} {eps.imag:11.3e} {S * abs(eps):9.4f} {flag:>1} "
                  f"{eps_t.real:11.3e} {eps_t.imag:11.3e} {S * abs(eps_t):9.4f} {dt:5.1f}")
    print("\n    S*|eps| by z (rows) and S (columns); word sum where unmarked, torus identity in cells marked *:")
    print(f"{'z':>22} " + " ".join(f"{S:>10.1f}" for S in Slist))
    best = {}
    for z in zlist:
        row = []
        for S in Slist:
            e = results_t[(z, S)] if flags[(z, S)] == '*' else results[(z, S)]
            best[(z, S)] = e
            row.append(f"{S * abs(e):9.4f}{flags[(z, S)]}")
        print(f"{str(np.round(z, 4)):>22} " + " ".join(row))
    print("    ratio of consecutive S*|eps| (near 1: |eps| ~ C/S; near 1/2 would mean a faster rate):")
    for z in zlist:
        r = [S2 * abs(best[(z, S2)]) / (S1 * abs(best[(z, S1)])) for S1, S2 in zip(Slist[:-1], Slist[1:])]
        print(f"{str(np.round(z, 4)):>22} " + " ".join(f"{x:10.4f}" for x in r))
    return results


def main():
    t_all = time.time()
    print("Hypothesis L check, faces with four states (|G| = 3), word sum against the complex-tilt prediction.")
    print("numpy", np.__version__)

    # (d) the dynamic program against a direct enumeration at small s and complex z
    print("\n(d) word dynamic program against direct enumeration (S = 2.5, L <= 32)")
    for Q, mu, nm in [(chain_cycle4()[0], chain_cycle4()[1], "cycle"), (chain_k4()[0], chain_k4()[1], "K4")]:
        fd = facet_data(Q, mu, [0, 1, 2], 3)
        beta = np.array([0.5, 0.3, 0.2])
        s = 2.5 * beta
        for z in [0.0, 0.1 + 0.07j, -0.12j]:
            A, d, muz, ez = weights(fd, z)
            l1, _, _ = log_H_words(A, muz, ez, s, 80)
            l2 = log_H_enum(A, muz, ez, s, 32)
            print(f"    {nm:6s} z = {z}: |H_dp/H_enum - 1| = {abs(np.exp(l1 - l2) - 1):.3e}")

    zlist = [0.0, 0.1, -0.1, 0.1j, -0.1j, 0.1 * np.exp(3j * pi / 4), 0.05 * np.exp(3j * pi / 4),
             0.2j, 0.2 * np.exp(1j * pi / 3)]
    Slist = [5.0, 10.0, 20.0, 40.0, 80.0, 160.0]

    # For the 4-cycle at beta = (0.5, 0.3, 0.2) the continued critical point folds on the negative
    # real axis at z = -0.066 (see check (c)), so the negative real test point is z = -0.05 there.
    Q, mu = chain_cycle4()
    zlist_cycle = [0.0, 0.1, -0.05, 0.1j, -0.1j, 0.1 * np.exp(3j * pi / 4), 0.05 * np.exp(3j * pi / 4),
                   0.2j, 0.2 * np.exp(1j * pi / 3)]
    run_chain("Non-reversible 4-cycle", Q, mu, [0.5, 0.3, 0.2], zlist_cycle, Slist)
    Q, mu = chain_k4()
    run_chain("Complete graph K4, non-reversible", Q, mu, [0.4, 0.35, 0.25], zlist, Slist)
    print(f"\ntotal time {time.time() - t_all:.0f} s")


if __name__ == "__main__":
    main()
