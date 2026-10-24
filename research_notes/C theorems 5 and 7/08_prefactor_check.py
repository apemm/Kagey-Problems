"""Prefactor matching and the Bessel ratio inequality for 08_T2_boundary_layer.md.
Run: py -I 08_prefactor_check.py > 08_prefactor_output.txt

(1) Reversible Q: C_F((1-e) beta, e) * e^{3/4} / C_G(beta)  ->  (4 pi)^{-1/2} (ab)^{1/4}  as e -> 0,
    with C_F from Proposition 4.2(b) of the draft (tree formula).
(2) The inequality I_0(Z)/I_1(Z) <= 1 + 2/Z on a grid (used in Proposition 2 of the note).
"""
import numpy as np
from itertools import combinations
from scipy.special import ive


def tree(cmat):
    """Weighted spanning-tree count by the matrix-tree theorem."""
    L = np.diag(cmat.sum(axis=1)) - cmat
    return np.linalg.det(L[1:, 1:])


def C_rev(Q, nu, mu, F, alpha):
    F = list(F)
    a = np.asarray(alpha, float)
    nF = nu[F]
    r = np.sqrt(a / nF); l = np.sqrt(a * nF)
    c = np.zeros((len(F), len(F)))
    for x in range(len(F)):
        for y in range(len(F)):
            if x != y:
                c[x, y] = np.sqrt(a[x] * a[y]) * Q[F[x], F[y]] * np.sqrt(nF[x] / nF[y])
    k = len(F)
    return (mu[F] @ r) * (l.sum()) / (4 * np.pi) ** ((k - 1) / 2) * np.sqrt(tree(c)) / np.prod(a)


nu = np.array([1., 2., 4.]); s = np.array([[0, 1, .5], [1, 0, 2], [.5, 2, 0]])
Q = s * np.sqrt(nu[None, :] / nu[:, None]); np.fill_diagonal(Q, -Q.sum(axis=1))
mu = np.array([1, 1, 1]) / 3.0
for beta in ([0.5, 0.5], [0.3, 0.7]):
    beta = np.array(beta)
    w = Q[2, :2] * Q[:2, 2]
    ab = np.sum(np.sqrt(w * beta)) ** 2
    target = (4 * np.pi) ** -0.5 * ab ** 0.25
    CG = C_rev(Q, nu, mu, [0, 1], beta)
    print(f"beta={beta}: target (4pi)^(-1/2) (ab)^(1/4) = {target:.6f}")
    for e in (1e-2, 1e-3, 1e-4, 1e-5, 1e-6):
        alpha = np.r_[(1 - e) * beta, e]
        CF = C_rev(Q, nu, mu, [0, 1, 2], alpha)
        print(f"   e={e:.0e}:  e^(3/4) C_F / C_G = {e**0.75 * CF / CG:.6f}")

Z = np.logspace(-6, 3, 2000)
ratio = ive(0, Z) / ive(1, Z)
print("max over grid of (I0/I1) / (1 + 2/Z) =", float(np.max(ratio / (1 + 2 / Z))))
print("max over grid of (I0/I1) / ((1 + sqrt(1+Z^2))/Z) =", float(np.max(ratio * Z / (1 + np.sqrt(1 + Z**2)))))
