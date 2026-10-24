"""Discrete check with the two-term amplitude for 08_T2_boundary_layer.md.
Run: py -I 08_layer_check3.py > 08_layer_output3.txt

R_lat2 = P_N(n) / [P_{N'}(n_hat) e^{-gamma2 x} (1-h q_i)^{n3} B_{n3}(abSh/(1-h q_i)) (1 + c1 rho I_0(Z)/I_1(Z))]
along the line n = ((N-n3)/2, (N-n3)/2, n3), at N = 400, 800 and T = 6, 10.
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
    "path 1-2-3 (rate 1)": (np.array([[-1, 1, 0], [1, -2, 1], [0, 1, -1.]]), 1.000000),
    "reversible, nu=(1,2,4)": (Qr, 3.303301),
    "non-reversible cycle": (np.array([[-3, 2, 1], [1, -3, 2], [2, 1, -3.]]), 3.996320),
}
G, i = [0, 1], 2
for name, (Q, c1) in chains.items():
    qi = -Q[i, i]
    cst = core.layer_constants(Q, G, i, [0.5, 0.5])
    for N in (400, 800):
        for T in (6., 10.):
            h = T / N
            PN, diag = core.exact_law_3(Q, mu, N, h)
            print(f"-- {name}, N={N}, T={T}: n3, x, R_cont, R_lat, R_lat2")
            for n3 in (2, 4, 8, 16, 32, 64, N // 8, N // 4):
                if (N - n3) % 2:
                    n3 += 1
                Np = N - n3; n1 = n2 = Np // 2
                x, S = h * n3, h * Np
                PG = diag[Np][n1]
                kc = h * PG * core.bessel_kernel(cst["ab"], S, x, cst["gamma"])
                w = cst["ab"] * S * h / (1 - h * qi)
                kl = PG * np.exp(-cst["gamma2"] * x) * (1 - h * qi) ** n3 * core.laguerre_B(n3, w)
                Z = 2 * np.sqrt(cst["ab"] * S * x); rho = np.sqrt(x / (S * cst["ab"]))
                amp = 1 + c1 * rho * ive(0, Z) / ive(1, Z)
                print(f"   {n3:5d} {x:7.4f}  {PN[n1, n2]/kc:9.5f}  {PN[n1, n2]/kl:9.5f}  {PN[n1, n2]/(kl*amp):9.5f}")
