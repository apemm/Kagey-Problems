"""Second set of checks for 08_T2_boundary_layer.md. Run: py -I 08_layer_check2.py > 08_layer_output2.txt

Part E: the amplitude derivative c1 = d/dz log C(beta, z) at z = 0, from the closed two-state
        amplitude and, for reversible chains, from the formula of Section 5 of the note.
Part F: continuum ratio with the two-term kernel  K(x) [1 + c1 rho I_0(Z)/I_1(Z)],
        rho = sqrt(x/(S ab)), Z = 2 sqrt(ab S x), at T up to 320.
Part G: the generalized kernel  e^{-q_i x} (1/2 pi i) oint e^{x/z} Phi_lead(z)(s) z^{-2} dz / f_G(s),
        where Phi_lead is the leading large-S form of Phi(z): this tests the deduction of the
        theorem from the complex-parameter local law (Lemma L), uniformly up to x = T/4.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from importlib import import_module
from scipy.special import ive
core = import_module("08_layer_core")

mu = np.array([1, 1, 1]) / 3.0
nu = np.array([1., 2., 4.]); s = np.array([[0, 1, .5], [1, 0, 2], [.5, 2, 0]])
Qr = s * np.sqrt(nu[None, :] / nu[:, None]); np.fill_diagonal(Qr, -Qr.sum(axis=1))
chains = {
    "path 1-2-3 (rate 1)": np.array([[-1, 1, 0], [1, -2, 1], [0, 1, -1.]]),
    "reversible, nu=(1,2,4)": Qr,
    "non-reversible cycle": np.array([[-3, 2, 1], [1, -3, 2], [2, 1, -3.]]),
}
G, i = [0, 1], 2


def Mz(Q, z):
    c = np.array([Q[0, i], Q[1, i]]); rv = np.array([Q[i, 0], Q[i, 1]])
    m12 = Q[0, 1] + z * c[0] * rv[1]; m21 = Q[1, 0] + z * c[1] * rv[0]
    d1 = -Q[0, 0] - z * c[0] * rv[0]; d2 = -Q[1, 1] - z * c[1] * rv[1]
    p1 = mu[0] + z * mu[i] * rv[0]; p2 = mu[1] + z * mu[i] * rv[1]
    e1 = 1 + z * c[0]; e2 = 1 + z * c[1]
    return m12, m21, d1, d2, p1, p2, e1, e2


def Phi_lead(Q, z, s1, s2, shift=0.0):
    """Leading large-S form of the two-state density: I_nu(Y) -> e^Y / sqrt(2 pi Y)."""
    m12, m21, d1, d2, p1, p2, e1, e2 = Mz(Q, z)
    m = m12 * m21
    Y = 2 * np.sqrt(m * s1 * s2)
    amp = (p1 * e1 * np.sqrt(m * s1 / s2) + p1 * m12 * e2 + p2 * m21 * e1
           + p2 * e2 * np.sqrt(m * s2 / s1))
    return np.exp(-d1 * s1 - d2 * s2 + Y + shift) * amp / np.sqrt(2 * np.pi * Y)


def logC(Q, z, beta):
    """log of the S-free amplitude of Phi(z) at profile beta (two-state closed form)."""
    m12, m21, d1, d2, p1, p2, e1, e2 = Mz(Q, z)
    m = m12 * m21
    amp = (p1 * e1 * np.sqrt(m * beta[0] / beta[1]) + p1 * m12 * e2 + p2 * m21 * e1
           + p2 * e2 * np.sqrt(m * beta[1] / beta[0]))
    return np.log(amp) - 0.25 * np.log(m * beta[0] * beta[1])


def c1_formula_reversible(Q, beta):
    """c1 = mu_i b/(mu_G . r) + a/(l . 1) + (1/2) d/dz log tree(c(beta, z)) for reversible Q."""
    cst = core.layer_constants(Q, G, i, beta)
    r, l = cst["r"], cst["l"]
    cvec = np.array([Q[0, i], Q[1, i]]); rv = np.array([Q[i, 0], Q[i, 1]])
    # tree of the two-state tilted conductance c_12(z) = l_1 M(z)_12 r_2 (reversible: r_z = r)
    c12 = l[0] * Q[0, 1] * r[1]
    dc12 = l[0] * cvec[0] * rv[1] * r[1]
    return mu[i] * cst["b"] / (mu[G] @ r) + cst["a"] / l.sum() + 0.5 * dc12 / c12


print("=== Part E: amplitude derivative c1 ===")
c1tab = {}
for name, Q in chains.items():
    for beta in ([0.5, 0.5], [0.3, 0.7]):
        dz = 1e-5
        c1 = (logC(Q, dz, beta) - logC(Q, -dz, beta)) / (2 * dz)
        c1tab[(name, tuple(beta))] = c1
        extra = ""
        if "non" not in name:
            extra = f"   formula (reversible) = {c1_formula_reversible(Q, beta):.6f}"
        print(f"{name:26s} beta={beta}: c1 (finite difference) = {c1:.6f}{extra}")
print()

xs_lab = ["0.01/T", "1/T", "0.1", "1", "3", "10", "T/10", "T/4"]
def xs(T):
    return [0.01 / T, 1 / T, 0.1, 1.0, 3.0, 10.0, T / 10, T / 4]

print("=== Part F: continuum ratio with the two-term Bessel kernel K(x)[1 + c1 rho I0/I1] ===")
for name, Q in chains.items():
    beta = [0.5, 0.5]
    cst = core.layer_constants(Q, G, i, beta)
    c1 = c1tab[(name, tuple(beta))]
    print(f"-- {name}, beta={beta}, ab={cst['ab']:.4f}, gamma={cst['gamma']:.4f}, c1={c1:.4f}")
    print("        T   " + "  ".join(f"{l:>10s}" for l in xs_lab))
    for T in (10., 20., 40., 80., 160., 320.):
        one, two = [], []
        for x in xs(T):
            if x >= T / 2:
                one.append(np.nan); two.append(np.nan); continue
            S = T - x
            s1, s2 = S * beta[0], S * beta[1]
            Z = 2 * np.sqrt(cst["ab"] * S * x); rho = np.sqrt(x / (S * cst["ab"]))
            qi = -Q[i, i]
            A = S * cst["IG"] + qi * x - Z
            fF, _ = core.fF_continuum(Q, mu, s1, s2, x, cst["ab"], npts=4096, shift=A)
            fG = core.fG_continuum(Q, mu, s1, s2, shift=S * cst["IG"])
            K = np.exp(-cst["gamma2"] * x) * np.sqrt(cst["ab"] * S / x) * ive(1, Z)
            one.append(fF / (fG * K))
            two.append(fF / (fG * K * (1 + c1 * rho * ive(0, Z) / ive(1, Z))))
        print(f"   1-term {T:5.0f} " + "  ".join(f"{v:10.6f}" for v in one))
        print(f"   2-term {T:5.0f} " + "  ".join(f"{v:10.6f}" for v in two))
print()

print("=== Part G: generalized kernel from the leading form of Phi(z) (tests Lemma L => Theorem) ===")
for name, Q in chains.items():
    beta = [0.5, 0.5]
    cst = core.layer_constants(Q, G, i, beta)
    print(f"-- {name}, beta={beta}")
    print("        T   " + "  ".join(f"{l:>10s}" for l in xs_lab))
    for T in (10., 20., 40., 80., 160., 320.):
        row = []
        for x in xs(T):
            if x >= T / 2:
                row.append(np.nan); continue
            S = T - x
            s1, s2 = S * beta[0], S * beta[1]
            Z = 2 * np.sqrt(cst["ab"] * S * x)
            qi = -Q[i, i]
            A = S * cst["IG"] + qi * x - Z
            fF, _ = core.fF_continuum(Q, mu, s1, s2, x, cst["ab"], npts=4096, shift=A)
            rho = np.sqrt(x / (S * cst["ab"]))
            npts = 4096
            th = 2 * np.pi * (np.arange(npts) + 0.5) / npts
            z = rho * np.exp(1j * th)
            vals = Phi_lead(Q, z, s1, s2, shift=A - qi * x) * np.exp(x / z) / z ** 2 * (1j * z)
            Kgen = np.real(vals.mean() * 2 * np.pi / (2j * np.pi))
            row.append(fF / Kgen)
        print(f"          {T:5.0f} " + "  ".join(f"{v:10.6f}" for v in row))
