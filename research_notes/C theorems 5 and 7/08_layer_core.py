"""Core routines for the boundary-layer note 08_T2_boundary_layer.md.

Setting: generator Q on d states, face F, state i in F, facet G = F minus {i}.
Everything here is for numerical checks only. Run with `py -I`.
"""
import numpy as np
from math import lgamma, log, exp
from scipy.special import iv, ive


# ---------------------------------------------------------------- tilt on G
def tilt(Q, G, beta, iters=200):
    """Optimal vector r_beta of the rate I_G(beta) (Prop. rate (b) of the draft).

    Maximizes Psi(psi) = sum beta_a q_a - sum_{a != b in G} beta_a q_ab e^{psi_b - psi_a}
    by Newton's method in psi (concave). Returns r (sum r = 1), l = beta / r, I_G(beta).
    """
    G = list(G)
    g = len(G)
    beta = np.asarray(beta, float)
    A = np.array([[Q[a, b] if a != b else 0.0 for b in G] for a in G])
    qG = np.array([-Q[a, a] for a in G])
    psi = np.zeros(g)
    for _ in range(iters):
        E = np.exp(psi[None, :] - psi[:, None])          # e^{psi_b - psi_a}
        W = beta[:, None] * A * E                         # w_ab
        grad = W.sum(axis=0) - W.sum(axis=1)              # gradient of sum w (to be minimized)
        # Hessian of sum w_ab e^{..}: Laplacian with conductance w_ab + w_ba
        C = W + W.T
        H = np.diag(C.sum(axis=1)) - C
        H[0, :] = 0.0; H[:, 0] = 0.0; H[0, 0] = 1.0       # fix psi_0 = 0
        gr = grad.copy(); gr[0] = 0.0
        step = np.linalg.solve(H, gr)
        psi -= step
        if np.max(np.abs(step)) < 1e-15:
            break
    r = np.exp(psi); r /= r.sum()
    l = beta / r
    E = np.exp(np.log(r)[None, :] - np.log(r)[:, None])
    IG = float(beta @ qG - (beta[:, None] * A * E).sum())
    return r, l, IG


def layer_constants(Q, G, i, beta):
    """a, b, ab, j2, gamma = q_i + j2/(ab) at the facet profile beta (Section 3 of the note)."""
    G = list(G)
    r, l, IG = tilt(Q, G, beta)
    c = np.array([Q[a, i] for a in G])      # entrance rates into i
    rv = np.array([Q[i, a] for a in G])     # exit rates from i into G
    a = float(c @ l)
    b = float(rv @ r)
    ab = a * b
    gradP = a * rv * r - b * c * l          # sums to zero
    A = np.array([[Q[x, y] if x != y else 0.0 for y in G] for x in G])
    K = l[:, None] * A * r[None, :]
    K = K + K.T
    L = np.diag(K.sum(axis=1)) - K
    j2 = 0.5 * float(gradP @ np.linalg.pinv(L) @ gradP)
    qi = -Q[i, i]
    entry = c * l / a
    exitlaw = rv * r / b
    return dict(r=r, l=l, IG=IG, a=a, b=b, ab=ab, j2=j2, gamma=qi + j2 / ab,
                gamma2=j2 / ab, entry=entry, exit=exitlaw)


def J_real(Q, G, i, beta, z):
    """J(beta, z) = I_{M(z)}(beta) for real z >= 0, M(z) = Q_G + z c r^T (self-loops in diagonal)."""
    G = list(G)
    c = np.array([Q[a, i] for a in G]); rv = np.array([Q[i, a] for a in G])
    QG = np.array([[Q[a, b] for b in G] for a in G])
    M = QG + z * np.outer(c, rv)
    # I_M(beta) = sup_u sum beta_a ( -(M u)_a / u_a ) ; off-diagonal part of M is nonnegative
    Mq = M.copy()
    d = -np.diag(Mq).copy()
    np.fill_diagonal(Mq, 0.0)
    g = len(G)
    QQ = np.zeros((g, g)); QQ[:, :] = Mq; np.fill_diagonal(QQ, -d)
    r, l, I = tilt(QQ, range(g), beta)
    return I


# ------------------------------------------------- two-state densities
def calI_scaled(y):
    """[I_1(2 sqrt y)/sqrt y] * exp(-|Re 2 sqrt y|), entire part scaled; complex y allowed."""
    y = np.asarray(y, complex)
    sq = np.sqrt(y)
    out = np.empty_like(y)
    small = np.abs(y) < 1e-8
    out[~small] = ive(1, 2 * sq[~small]) / sq[~small]
    out[small] = 1.0 + y[small] / 2.0
    return out


def two_state_density(m12, m21, d1, d2, p1, p2, e1, e2, s1, s2, shift=0.0):
    """exp(shift) times the occupation density (in s2) of a two-state Metzler matrix on paths
    that visit both states. Off-diagonal m12, m21, diagonal -d1, -d2, start (p1, p2), end (e1, e2).
    Complex inputs allowed. Scaled Bessel functions avoid overflow."""
    m = m12 * m21
    y = m * s1 * s2
    w = 2 * np.sqrt(np.asarray(y, complex))
    val = ((p1 * e1 * m * s1 + p2 * e2 * m * s2) * calI_scaled(y)
           + (p1 * m12 * e2 + p2 * m21 * e1) * ive(0, w))
    return np.exp(-d1 * s1 - d2 * s2 + np.abs(np.real(w)) + shift) * val


def Phi(Q, mu, z, s1, s2, i=2, shift=0.0):
    """Phi(z)(s) for G = {0,1}, i = 2: the K-generating function of the exact layer representation."""
    c = np.array([Q[0, i], Q[1, i]]); rv = np.array([Q[i, 0], Q[i, 1]])
    m12 = Q[0, 1] + z * c[0] * rv[1]
    m21 = Q[1, 0] + z * c[1] * rv[0]
    d1 = -Q[0, 0] - z * c[0] * rv[0]
    d2 = -Q[1, 1] - z * c[1] * rv[1]
    p1 = mu[0] + z * mu[i] * rv[0]
    p2 = mu[1] + z * mu[i] * rv[1]
    e1 = 1 + z * c[0]
    e2 = 1 + z * c[1]
    return two_state_density(m12, m21, d1, d2, p1, p2, e1, e2, s1, s2, shift)


def fF_continuum(Q, mu, s1, s2, x, ab_guess, npts=1024, shift=0.0):
    """Exact continuum density of (s2, x) on E_F, F = {0,1,2}, via
    e^{q_i x} f_F(s,x) = (1/2 pi i) oint e^{x/z} Phi(z)(s) z^{-2} dz   (Lemma 1 of the note)."""
    S = s1 + s2
    rho = np.sqrt(x / (S * ab_guess))
    qi_ = -Q[2, 2]
    th = 2 * np.pi * (np.arange(npts) + 0.5) / npts
    z = rho * np.exp(1j * th)
    vals = Phi(Q, mu, z, s1, s2, shift=shift - qi_ * x, i=2) * np.exp(x / z) / z ** 2 * (1j * z)
    integral = vals.mean() * 2 * np.pi / (2j * np.pi)
    return float(np.real(integral)), float(abs(np.imag(integral)))


def fG_continuum(Q, mu, s1, s2, shift=0.0):
    return float(np.real(Phi(Q, mu, 0.0, s1, s2, shift=shift)))


def bessel_kernel(ab, S, x, gamma):
    """e^{-gamma x} sqrt(ab S / x) I_1(2 sqrt(ab S x)), computed with the scaled Bessel function."""
    Z = 2 * np.sqrt(ab * S * x)
    return np.exp(-gamma * x + Z) * np.sqrt(ab * S / x) * ive(1, Z)


def laguerre_B(a, w):
    """B_a(w) = sum_{m=1}^a binom(a-1, m-1) w^m / m!   (the draft's eq. refresh-polynomial)."""
    if w <= 0:
        return 0.0
    logs = [lgamma(a) - lgamma(m) - lgamma(a - m + 1) + m * log(w) - lgamma(m + 1)
            for m in range(1, a + 1)]
    mx = max(logs)
    return exp(mx) * sum(exp(t - mx) for t in logs)


# ------------------------------------------------- exact discrete law (three states)
def exact_law_3(Q, mu, N, h):
    """Dynamic programming for the composition law of the chain I + hQ on 3 states.

    Returns (PN, diag) where PN[n1, n2] = P_N(n1, n2, N - n1 - n2) and
    diag[t][n1] = P_t(n1, t - n1, 0) for t = 1..N (paths that stay in {0,1}).
    """
    P = np.eye(3) + h * Q
    A = np.zeros((3, N + 2, N + 2))
    A[0, 1, 0] = mu[0]; A[1, 0, 1] = mu[1]; A[2, 0, 0] = mu[2]
    diag = [None, np.array([A[0, n1, 1 - n1] + A[1, n1, 1 - n1] + A[2, n1, 1 - n1]
                            for n1 in range(2)])]
    for t in range(2, N + 1):
        B = np.zeros_like(A)
        m = t + 1
        for s in range(3):
            src = A[s, :m, :m]
            B[0, 1:m + 1, :m] += P[s, 0] * src
            B[1, :m, 1:m + 1] += P[s, 1] * src
            B[2, :m, :m] += P[s, 2] * src
        A = B
        tot = A.sum(axis=0)
        n1 = np.arange(t + 1)
        diag.append(tot[n1, t - n1].copy())
    PN = A.sum(axis=0)
    return PN, diag
