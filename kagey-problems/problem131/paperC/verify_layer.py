"""Numerical checks of the boundary layer, Section `sec:boundary-layer` (Section `sec:layer-numerics`).

Three chains with three states, the facet G = {1,2} of the face F = {1,2,3}, the state i = 3
and the uniform start: the path 1-2-3 with unit rates, a reversible chain with stationary weights
nu = (1,2,4), and the non-reversible cycle q12 = q23 = q31 = 2, q21 = q32 = q13 = 1.

  A. The layer constants of Proposition `prop:layer-constants` at beta = (1/2,1/2) and (0.3,0.7):
     omega_beta = a b, gamma_beta = q_i + j_2/omega_beta, the entrance and exit laws, and
     finite differences of z -> J_G(beta,z) at z = 0 against -omega_beta and j_2.
  B. The contour formula `eq:layer-contour` with the closed two-state density of Lemma `lem:L-two`
     against the exact discrete law P_N(n)/h^2 (dynamic program), at T = 6 and N = 200, 400, 800.
  E. The first amplitude correction c_1 = d/dz log C_G(beta,z) at z = 0, by a central difference
     of the closed two-state amplitude, against formula `eq:layer-c1` for the reversible chains.
  F. The ratio f_F / (f_G B), with the one-term Bessel kernel B and with the two-term kernel
     B (1 + c_1 rho I_0/I_1) of Theorem `thm:layer`(c), for T = 10 to 320 and x from 0.01/T to T/4.
  G. The generalized kernel (the contour integral of the leading large-S form of f_G^(z)) against
     f_F/f_G, for the same cells.
  H. On the lattice, the Laguerre kernel of Remark `rem:layer-discrete` with the two-term amplitude
     against the exact law at n_3 = 2, N = 400 and 800, T = 6 and 10.
  I. Proposition `prop:layer-prefactor` for the reversible chain, as epsilon -> 0, and the
     inequality I_0(Z)/I_1(Z) <= 1 + 2/Z on a logarithmic grid of Z in [1e-6, 1e3].
  J. The non-reversible cycle at x = 0.05 T and T = 800, 1600, 3200, where the relative Bessel form
     fails (the paragraph after Theorem `thm:layer`).

Every check is an assertion. Nothing in the section is deduced from these numbers.
Needs numpy and scipy. Run:  py -I verify_layer.py   (about two minutes)
"""
from math import exp, lgamma, log

import numpy as np
from scipy.special import ive

CHECKS = 0


def ok(cond, what):
    global CHECKS
    if not cond:
        raise AssertionError(what)
    CHECKS += 1
    print("  ok   ", what, flush=True)


# ---------------------------------------------------------------- tilt on G
def tilt(Q, G, beta, iters=200):
    """Optimal vector r_beta of the rate J_G(beta), by Newton's method on the concave dual."""
    G = list(G)
    g = len(G)
    beta = np.asarray(beta, float)
    A = np.array([[Q[a, b] if a != b else 0.0 for b in G] for a in G])
    qG = np.array([-Q[a, a] for a in G])
    psi = np.zeros(g)
    for _ in range(iters):
        E = np.exp(psi[None, :] - psi[:, None])
        W = beta[:, None] * A * E
        grad = W.sum(axis=0) - W.sum(axis=1)
        C = W + W.T
        H = np.diag(C.sum(axis=1)) - C
        H[0, :] = 0.0
        H[:, 0] = 0.0
        H[0, 0] = 1.0
        gr = grad.copy()
        gr[0] = 0.0
        step = np.linalg.solve(H, gr)
        psi -= step
        if np.max(np.abs(step)) < 1e-15:
            break
    r = np.exp(psi)
    r /= r.sum()
    l = beta / r
    E = np.exp(np.log(r)[None, :] - np.log(r)[:, None])
    JG = float(beta @ qG - (beta[:, None] * A * E).sum())
    return r, l, JG


def layer_constants(Q, G, i, beta):
    G = list(G)
    r, l, JG = tilt(Q, G, beta)
    c = np.array([Q[a, i] for a in G])
    rv = np.array([Q[i, a] for a in G])
    a = float(c @ l)
    b = float(rv @ r)
    ab = a * b
    gradP = a * rv * r - b * c * l
    A = np.array([[Q[x, y] if x != y else 0.0 for y in G] for x in G])
    K = l[:, None] * A * r[None, :]
    K = K + K.T
    L = np.diag(K.sum(axis=1)) - K
    j2 = 0.5 * float(gradP @ np.linalg.pinv(L) @ gradP)
    qi = -Q[i, i]
    return dict(r=r, l=l, JG=JG, a=a, b=b, ab=ab, j2=j2, gamma=qi + j2 / ab,
                gamma2=j2 / ab, entry=c * l / a, exit=rv * r / b)


def J_real(Q, G, i, beta, z):
    """J_G(beta, z), the rate of Q_G + z c r^T, for real z >= 0."""
    G = list(G)
    c = np.array([Q[a, i] for a in G])
    rv = np.array([Q[i, a] for a in G])
    QG = np.array([[Q[a, b] for b in G] for a in G])
    M = QG + z * np.outer(c, rv)
    return tilt(M, range(len(G)), beta)[2]


# ------------------------------------------------- two-state densities
def calI_scaled(y):
    y = np.asarray(y, complex)
    sq = np.sqrt(y)
    out = np.empty_like(y)
    small = np.abs(y) < 1e-8
    out[~small] = ive(1, 2 * sq[~small]) / sq[~small]
    out[small] = 1.0 + y[small] / 2.0
    return out


def two_state_density(m12, m21, d1, d2, p1, p2, e1, e2, s1, s2, shift=0.0, extra=0.0):
    """exp(shift + extra) times the occupation density of a two-state Metzler matrix on paths that
    visit both states (Lemma lem:L-two). Complex inputs allowed; scaled Bessel functions and the
    complex exponent `extra` inside the same exponential avoid overflow."""
    m = m12 * m21
    y = m * s1 * s2
    w = 2 * np.sqrt(np.asarray(y, complex))
    val = ((p1 * e1 * m * s1 + p2 * e2 * m * s2) * calI_scaled(y)
           + (p1 * m12 * e2 + p2 * m21 * e1) * ive(0, w))
    return np.exp(-d1 * s1 - d2 * s2 + np.abs(np.real(w)) + shift + extra) * val


def Mz(Q, mu, z, i=2):
    c = np.array([Q[0, i], Q[1, i]])
    rv = np.array([Q[i, 0], Q[i, 1]])
    return (Q[0, 1] + z * c[0] * rv[1], Q[1, 0] + z * c[1] * rv[0],
            -Q[0, 0] - z * c[0] * rv[0], -Q[1, 1] - z * c[1] * rv[1],
            mu[0] + z * mu[i] * rv[0], mu[1] + z * mu[i] * rv[1], 1 + z * c[0], 1 + z * c[1])


def Phi(Q, mu, z, s1, s2, shift=0.0, extra=0.0):
    """f_G^{(z)}(s) for G = {1,2}, i = 3."""
    return two_state_density(*Mz(Q, mu, z), s1, s2, shift, extra)


def fF_continuum(Q, mu, s1, s2, x, ab_guess, npts=1024, shift=0.0, radius=1.0):
    """exp(shift) f_F(s, x) by the contour formula eq:layer-contour on |z| = radius * rho."""
    S = s1 + s2
    rho = radius * np.sqrt(x / (S * ab_guess))
    qi = -Q[2, 2]
    th = 2 * np.pi * (np.arange(npts) + 0.5) / npts
    z = rho * np.exp(1j * th)
    vals = Phi(Q, mu, z, s1, s2, shift=shift - qi * x, extra=x / z) / z ** 2 * (1j * z)
    integral = vals.mean() * 2 * np.pi / (2j * np.pi)
    return float(np.real(integral)), float(abs(np.imag(integral)))


def fG_continuum(Q, mu, s1, s2, shift=0.0):
    return float(np.real(Phi(Q, mu, 0.0, s1, s2, shift=shift)))


def Phi_lead(Q, mu, z, s1, s2, shift=0.0, extra=0.0):
    """Leading large-S form of f_G^{(z)}: I_nu(Y) replaced by e^Y / sqrt(2 pi Y)."""
    m12, m21, d1, d2, p1, p2, e1, e2 = Mz(Q, mu, z)
    m = m12 * m21
    Y = 2 * np.sqrt(m * s1 * s2)
    amp = (p1 * e1 * np.sqrt(m * s1 / s2) + p1 * m12 * e2 + p2 * m21 * e1
           + p2 * e2 * np.sqrt(m * s2 / s1))
    return np.exp(-d1 * s1 - d2 * s2 + Y + shift + extra) * amp / np.sqrt(2 * np.pi * Y)


def logC(Q, mu, z, beta):
    m12, m21, d1, d2, p1, p2, e1, e2 = Mz(Q, mu, z)
    m = m12 * m21
    amp = (p1 * e1 * np.sqrt(m * beta[0] / beta[1]) + p1 * m12 * e2 + p2 * m21 * e1
           + p2 * e2 * np.sqrt(m * beta[1] / beta[0]))
    return np.log(amp) - 0.25 * np.log(m * beta[0] * beta[1])


def laguerre_B(a, w):
    """B_a(w) = sum_{m=1}^a binom(a-1, m-1) w^m / m!."""
    logs = [lgamma(a) - lgamma(m) - lgamma(a - m + 1) + m * log(w) - lgamma(m + 1)
            for m in range(1, a + 1)]
    mx = max(logs)
    return exp(mx) * sum(exp(t - mx) for t in logs)


def exact_law_3(Q, mu, N, h):
    """Composition law of the chain I + hQ on 3 states. PN[n1, n2] = P_N(n1, n2, N-n1-n2), and
    diag[t][n1] = P_t(n1, t-n1, 0) for the paths of length t that stay in {1,2}."""
    P = np.eye(3) + h * Q
    A = np.zeros((3, N + 2, N + 2))
    A[0, 1, 0] = mu[0]
    A[1, 0, 1] = mu[1]
    A[2, 0, 0] = mu[2]
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
    return A.sum(axis=0), diag


def tree(cmat):
    L = np.diag(cmat.sum(axis=1)) - cmat
    return np.linalg.det(L[1:, 1:])


def C_rev(Q, nu, mu, F, alpha):
    """C_F(alpha) for reversible Q by Proposition prop:constant(b)."""
    F = list(F)
    a = np.asarray(alpha, float)
    nF = nu[F]
    r = np.sqrt(a / nF)
    l = np.sqrt(a * nF)
    c = np.zeros((len(F), len(F)))
    for x in range(len(F)):
        for y in range(len(F)):
            if x != y:
                c[x, y] = np.sqrt(a[x] * a[y]) * Q[F[x], F[y]] * np.sqrt(nF[x] / nF[y])
    k = len(F)
    return (mu[F] @ r) * l.sum() / (4 * np.pi) ** ((k - 1) / 2) * np.sqrt(tree(c)) / np.prod(a)


# ------------------------------------------------------------------ data
mu = np.array([1, 1, 1]) / 3.0
nu = np.array([1., 2., 4.])
s_sym = np.array([[0, 1, .5], [1, 0, 2], [.5, 2, 0]])
Qr = s_sym * np.sqrt(nu[None, :] / nu[:, None])
np.fill_diagonal(Qr, -Qr.sum(axis=1))
CHAINS = {
    "path 1-2-3": np.array([[-1, 1, 0], [1, -2, 1], [0, 1, -1.]]),
    "reversible nu=(1,2,4)": Qr,
    "non-reversible cycle": np.array([[-3, 2, 1], [1, -3, 2], [2, 1, -3.]]),
}
REV = ("path 1-2-3", "reversible nu=(1,2,4)")
G, I = [0, 1], 2


def ratios_continuum(Q, beta, T, x, c1, npts=4096):
    """f_F/(f_G B) with the one-term and the two-term kernel, and f_F over the generalized kernel."""
    cst = layer_constants(Q, G, I, beta)
    S = T - x
    s1, s2 = S * beta[0], S * beta[1]
    Z = 2 * np.sqrt(cst["ab"] * S * x)
    rho = np.sqrt(x / (S * cst["ab"]))
    qi = -Q[I, I]
    A = S * cst["JG"] + qi * x - Z
    fF, _ = fF_continuum(Q, mu, s1, s2, x, cst["ab"], npts=npts, shift=A)
    fG = fG_continuum(Q, mu, s1, s2, shift=S * cst["JG"])
    K = np.exp(-cst["gamma2"] * x) * np.sqrt(cst["ab"] * S / x) * ive(1, Z)
    one = fF / (fG * K)
    two = fF / (fG * K * (1 + c1 * rho * ive(0, Z) / ive(1, Z)))
    th = 2 * np.pi * (np.arange(npts) + 0.5) / npts
    z = rho * np.exp(1j * th)
    vals = Phi_lead(Q, mu, z, s1, s2, shift=A - qi * x, extra=x / z) / z ** 2 * (1j * z)
    Kgen = np.real(vals.mean() * 2 * np.pi / (2j * np.pi))
    return one, two, fF / Kgen


def main():
    print("A. The layer constants (G = {1,2}, i = 3)")
    for name, Q in CHAINS.items():
        for beta in ([0.5, 0.5], [0.3, 0.7]):
            c = layer_constants(Q, G, I, beta)
            z = 1e-3
            J0, J1, J2 = (J_real(Q, G, I, beta, k * z) for k in range(3))
            dJ = (4 * J1 - 3 * J0 - J2) / (2 * z)
            d2J = (J2 - 2 * J1 + J0) / (2 * z * z)
            ok(abs(dJ + c["ab"]) < 1e-4 * c["ab"] and abs(d2J - c["j2"]) < 0.02,
               f"{name}, beta = {beta}: -dJ/dz(0) = {-dJ:.6f} vs omega = {c['ab']:.6f}, "
               f"d2J/dz2(0)/2 = {d2J:.4f} vs omega(gamma - q_i) = {c['j2']:.4f}")
            if name in REV:
                w = Q[I, G] * Q[G, I]
                ok(c["gamma2"] < 1e-9 and abs(np.sum(np.sqrt(w * np.array(beta))) ** 2 - c["ab"]) < 1e-10
                   and np.allclose(c["entry"], c["exit"]),
                   f"{name}, beta = {beta}: reversible, gamma = q_i, omega = (sum_j sqrt(w_ij beta_j))^2, "
                   f"entrance law = exit law")
    c = layer_constants(CHAINS["non-reversible cycle"], G, I, [0.5, 0.5])
    ok(round(c["ab"], 4) == 5.1820 and round(c["gamma"], 4) == 3.4179,
       f"non-reversible cycle at beta = (1/2,1/2): omega = {c['ab']:.4f}, gamma = {c['gamma']:.4f}, q_3 = 3")

    print("B. The contour formula against the exact discrete law, T = 6")
    for name in ("path 1-2-3", "non-reversible cycle"):
        Q = CHAINS[name]
        T = 6.0
        errs = []
        for N in (200, 400, 800):
            h = T / N
            PN, _ = exact_law_3(Q, mu, N, h)
            n3 = N // 10
            n1 = (N - n3) * 2 // 5
            n2 = N - n3 - n1
            cst = layer_constants(Q, G, I, [n1 / (n1 + n2), n2 / (n1 + n2)])
            fF, im = fF_continuum(Q, mu, h * n1, h * n2, h * n3, cst["ab"])
            errs.append(abs(PN[n1, n2] / h ** 2 / fF - 1))
            ok(errs[-1] <= T * T / N and im < 1e-12,
               f"{name}, N = {N}, n = ({n1},{n2},{n3}): |P_N/h^2 / f_F - 1| = {errs[-1]:.2e} <= T^2/N")
        ok(errs[0] > errs[1] > errs[2], f"{name}: the error decreases with N")

    print("E. The first amplitude correction c_1")
    c1tab = {}
    for name, Q in CHAINS.items():
        for beta in ([0.5, 0.5], [0.3, 0.7]):
            dz = 1e-5
            c1 = (logC(Q, mu, dz, beta) - logC(Q, mu, -dz, beta)) / (2 * dz)
            c1tab[(name, tuple(beta))] = c1
            if name in REV:
                cst = layer_constants(Q, G, I, beta)
                r, l = cst["r"], cst["l"]
                cv = np.array([Q[0, I], Q[1, I]])
                rv = np.array([Q[I, 0], Q[I, 1]])
                c12 = l[0] * Q[0, 1] * r[1]
                dc12 = l[0] * cv[0] * rv[1] * r[1]
                formula = mu[I] * cst["b"] / (mu[G] @ r) + cst["a"] / l.sum() + 0.5 * dc12 / c12
                ok(abs(formula - c1) < 1e-6,
                   f"{name}, beta = {beta}: c_1 = {c1:.6f} (difference) = {formula:.6f} (eq:layer-c1)")
            else:
                print(f"         {name}, beta = {beta}: c_1 = {c1:.6f} (difference only)")

    print("F, G. Continuum ratios at beta = (1/2,1/2)")
    beta = [0.5, 0.5]
    Ts = (10., 20., 40., 80., 160., 320.)
    xs = lambda T: [0.01 / T, 1 / T, 0.1, 1.0, 3.0, 10.0, T / 10, T / 4]
    for name, Q in CHAINS.items():
        c1 = c1tab[(name, tuple(beta))]
        two_tab, gen_worst = {}, 0.0
        for T in Ts:
            for x in xs(T):
                if x >= T / 2:
                    continue
                one, two, gen = ratios_continuum(Q, beta, T, x, c1)
                two_tab[(T, x)] = two
                gen_worst = max(gen_worst, abs(gen - 1) * T)
        ok(gen_worst < 0.25, f"{name}: generalized kernel, max over the cells of T |ratio - 1| = {gen_worst:.3f}")
        if name in REV:
            worst = max(abs(v - 1) * T / (1 + x) for (T, x), v in two_tab.items())
            ok(worst < 1, f"{name}: two-term kernel, max over the cells of |ratio - 1| T/(1+x) = {worst:.3f}")
            halv = [abs(two_tab[(T, x)] - 1) / abs(two_tab[(2 * T, x)] - 1)
                    for T in (40., 80., 160.) for x in (0.1, 1.0, 3.0)]
            ok(min(halv) > 1.6 and max(halv) < 2.4,
               f"{name}: at x = 0.1, 1, 3 the two-term error halves when T doubles (factors {min(halv):.2f} to {max(halv):.2f})")
        else:
            print(f"         {name}: two-term ratio at x = T/4, T = 320: {two_tab[(320., 80.)]:.1f} (no Bessel form there)")

    print("H. The Laguerre kernel with the two-term amplitude at n_3 = 2")
    vals = []
    for name, Q in CHAINS.items():
        qi = -Q[I, I]
        cst = layer_constants(Q, G, I, [0.5, 0.5])
        c1 = c1tab[(name, (0.5, 0.5))]
        for N in (400, 800):
            for T in (6., 10.):
                h = T / N
                PN, diag = exact_law_3(Q, mu, N, h)
                n3 = 2
                Np = N - n3
                n1 = Np // 2
                x, S = h * n3, h * Np
                w = cst["ab"] * S * h / (1 - h * qi)
                kl = diag[Np][n1] * np.exp(-cst["gamma2"] * x) * (1 - h * qi) ** n3 * laguerre_B(n3, w)
                Z = 2 * np.sqrt(cst["ab"] * S * x)
                rho = np.sqrt(x / (S * cst["ab"]))
                R = PN[n1, n1] / (kl * (1 + c1 * rho * ive(0, Z) / ive(1, Z)))
                vals.append(R)
                print(f"         {name}, N = {N}, T = {T}: ratio {R:.5f}")
    ok(0.002 <= min(abs(v - 1) for v in vals) and max(abs(v - 1) for v in vals) <= 0.04,
       f"the 12 ratios are within {100 * min(abs(v - 1) for v in vals):.1f} to "
       f"{100 * max(abs(v - 1) for v in vals):.1f} percent of 1")

    print("I. Prefactor matching and the Bessel ratio")
    for beta in ([0.5, 0.5], [0.3, 0.7]):
        beta = np.array(beta)
        w = Qr[2, :2] * Qr[:2, 2]
        target = (4 * np.pi) ** -0.5 * np.sum(np.sqrt(w * beta)) ** 0.5
        CG = C_rev(Qr, nu, mu, [0, 1], beta)
        rel = []
        for e in (1e-2, 1e-3, 1e-4, 1e-5, 1e-6):
            CF = C_rev(Qr, nu, mu, [0, 1, 2], np.r_[(1 - e) * beta, e])
            rel.append(abs(e ** 0.75 * CF / CG / target - 1) / np.sqrt(e))
        ok(max(rel) < 3, f"beta = ({beta[0]}, {beta[1]}): |e^(3/4) C_F/C_G / ((4 pi)^(-1/2) omega^(1/4)) - 1| "
                         f"<= {max(rel):.2f} sqrt(e) for e = 1e-2 to 1e-6")
    Z = np.logspace(-6, 3, 2000)
    m = float(np.max(ive(0, Z) / ive(1, Z) / (1 + 2 / Z)))
    ok(m <= 1, f"max over the grid of (I_0/I_1)/(1 + 2/Z) = {m:.12f} <= 1")

    print("J. The non-reversible cycle at x = 0.05 T")
    Q = CHAINS["non-reversible cycle"]
    expected = {800.: 19.6, 1600.: 265., 3200.: 48268.}
    for T, val in expected.items():
        x = 0.05 * T
        cst = layer_constants(Q, G, I, [0.5, 0.5])
        S = T - x
        Zb = 2 * np.sqrt(cst["ab"] * S * x)
        A = S * cst["JG"] + 3.0 * x - Zb
        fF1, _ = fF_continuum(Q, mu, S / 2, S / 2, x, cst["ab"], npts=65536, shift=A)
        fF2, _ = fF_continuum(Q, mu, S / 2, S / 2, x, cst["ab"], npts=131072, shift=A)
        rho = np.sqrt(x / (S * cst["ab"]))
        th = 2 * np.pi * (np.arange(65536) + 0.5) / 65536
        zz = rho * np.exp(1j * th)
        vals = Phi(Q, mu, zz, S / 2, S / 2, shift=A - 3.0 * x, extra=x / zz) / zz ** 2 * (1j * zz)
        cancel = np.abs(vals).max() / abs(fF1)
        fG = fG_continuum(Q, mu, S / 2, S / 2, shift=S * cst["JG"])
        K = np.exp(-cst["gamma2"] * x) * np.sqrt(cst["ab"] * S / x) * ive(1, Zb)
        r = fF1 / (fG * K)
        bound = np.sqrt(x / T) * (1 + x)
        ok(abs(fF1 / fF2 - 1) < 1e-10 and cancel < 1e6 and abs(r / val - 1) < 0.01,
           f"T = {T:.0f}: f_F/(f_G B) = {r:.4g} (text {val}), sqrt(x/T)(1+x) = {bound:.1f}, "
           f"log of the ratio {np.log(r):.1f}; 65536 and 131072 nodes agree, largest term / result = {cancel:.0f}")
    print(f"verify_layer: all {CHECKS} checks passed")


if __name__ == "__main__":
    main()
