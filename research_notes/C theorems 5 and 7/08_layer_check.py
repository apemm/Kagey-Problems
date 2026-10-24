"""Numerical checks for 08_T2_boundary_layer.md. Run: py -I 08_layer_check.py > 08_layer_output.txt

Part A: constants a, b, gamma for three chains, and J''(0) by finite differences.
Part B: the exact layer representation (contour formula) against the discrete law at large N.
Part C: continuum ratio  f_F(s,x) / [ f_G(s) * Bessel kernel ]  for T = 6, 10, 20, 40, 80.
Part D: discrete ratio  P_N(n) / [ h P_{N'}(n_hat) * kernel ]  at N = 400, 800 and T = 6, 10,
        for the continuum kernel and for the Laguerre (lattice) kernel.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from importlib import import_module
core = import_module("08_layer_core")

np.set_printoptions(precision=6, suppress=True)
mu = np.array([1, 1, 1]) / 3.0
chains = {
    "path 1-2-3 (rate 1)": np.array([[-1, 1, 0], [1, -2, 1], [0, 1, -1.]]),
    "reversible, nu=(1,2,4)": None,
    "non-reversible cycle": np.array([[-3, 2, 1], [1, -3, 2], [2, 1, -3.]]),
}
# reversible chain: q_ab = s_ab sqrt(nu_b / nu_a) with symmetric s
nu = np.array([1., 2., 4.]); s = np.array([[0, 1, .5], [1, 0, 2], [.5, 2, 0]])
Qr = s * np.sqrt(nu[None, :] / nu[:, None]); np.fill_diagonal(Qr, -Qr.sum(axis=1))
chains["reversible, nu=(1,2,4)"] = Qr

G, i = [0, 1], 2

print("=== Part A: layer constants at facet profiles (G = {1,2}, i = 3) ===")
for name, Q in chains.items():
    for beta in ([0.5, 0.5], [0.3, 0.7]):
        c = core.layer_constants(Q, G, i, beta)
        z = 1e-3
        J0, J1, J2 = (core.J_real(Q, G, i, beta, k * z) for k in range(3))
        print(f"{name:26s} beta={beta}: ab={c['ab']:.6f}  -J'(0)~{(4*J1-3*J0-J2)/(2*z):.6f}  "
              f"j2={c['j2']:.6f}  J''(0)/2~{(J2-2*J1+J0)/(2*z*z):.4f}  gamma={c['gamma']:.6f}  "
              f"gamma2={c['gamma2']:.6f}  entry={c['entry']}  exit={c['exit']}")
        if "rev" in name or "path" in name:
            w = Q[i, G] * Q[G, i]
            print(f"{'':26s} reversible check (sum_j sqrt(w_ij beta_j))^2 = {np.sum(np.sqrt(w*np.array(beta)))**2:.6f}")
print()

print("=== Part B: contour formula for the continuum density vs discrete law P_N(n)/h^2 ===")
for name in ("path 1-2-3 (rate 1)", "non-reversible cycle"):
    Q = chains[name]
    T = 6.0
    for N in (200, 400, 800):
        h = T / N
        PN, diag = core.exact_law_3(Q, mu, N, h)
        n3 = N // 10; n1 = (N - n3) * 2 // 5; n2 = N - n3 - n1
        s1, s2, x = h * n1, h * n2, h * n3
        cst = core.layer_constants(Q, G, i, [n1 / (n1 + n2), n2 / (n1 + n2)])
        fF, err = core.fF_continuum(Q, mu, s1, s2, x, cst["ab"])
        print(f"{name:22s} T={T} N={N}: n=({n1},{n2},{n3})  P_N/h^2={PN[n1, n2]/h**2:.8e}  "
              f"contour f_F={fF:.8e}  ratio={PN[n1, n2]/h**2/fF:.6f}  (imag residue {err:.1e})")
print("(the ratio should approach 1 like O(T^2/N))")
print()

print("=== Part C: continuum layer ratio f_F(s,x) / [f_G(s) e^{-gamma x} sqrt(abS/x) I_1(2 sqrt(abSx))] ===")
for name, Q in chains.items():
    for beta in ([0.5, 0.5], [0.3, 0.7]):
        cst = core.layer_constants(Q, G, i, beta)
        print(f"-- {name}, beta={beta}, ab={cst['ab']:.4f}, gamma={cst['gamma']:.4f} (q_i={-Q[i,i]:.4f})")
        print("      T      x=0.01/T     x=0.3/T      x=1/T        x=3/T        x=0.1      x=0.3        x=1          x=3          x=T/10       x=T/4")
        for T in (6., 10., 20., 40., 80.):
            row = []
            for x in (0.01 / T, 0.3 / T, 1 / T, 3 / T, 0.1, 0.3, 1.0, 3.0, T / 10, T / 4):
                S = T - x
                s1, s2 = S * beta[0], S * beta[1]
                fF, _ = core.fF_continuum(Q, mu, s1, s2, x, cst["ab"], npts=2048)
                fG = core.fG_continuum(Q, mu, s1, s2)
                row.append(fF / (fG * core.bessel_kernel(cst["ab"], S, x, cst["gamma"])))
            print(f"   {T:5.0f}  " + "  ".join(f"{v:10.6f}" for v in row))
        if cst["gamma2"] > 1e-9:
            print("   same with gamma replaced by q_i (no gamma2 correction):")
            for T in (10., 40., 80.):
                row = []
                for x in (0.01 / T, 0.3 / T, 1 / T, 3 / T, 0.1, 0.3, 1.0, 3.0, T / 10, T / 4):
                    S = T - x
                    s1, s2 = S * beta[0], S * beta[1]
                    fF, _ = core.fF_continuum(Q, mu, s1, s2, x, cst["ab"], npts=2048)
                    fG = core.fG_continuum(Q, mu, s1, s2)
                    row.append(fF / (fG * core.bessel_kernel(cst["ab"], S, x, -Q[i, i])))
                print(f"   {T:5.0f}  " + "  ".join(f"{v:10.6f}" for v in row))
print()

print("=== Part D: discrete ratios along the line n = ((N-n3)/2, (N-n3)/2, n3) from the edge {1,2} ===")
print("R_cont = P_N(n) / [h P_{N-n3}(n_hat) e^{-gamma x} sqrt(abS/x) I_1(2 sqrt(abSx))]")
print("R_lat  = P_N(n) / [P_{N-n3}(n_hat) e^{-gamma2 x} (1-h q_i)^{n3} B_{n3}(abSh/(1-h q_i))]")
for name in ("path 1-2-3 (rate 1)", "reversible, nu=(1,2,4)", "non-reversible cycle"):
    Q = chains[name]
    qi = -Q[i, i]
    for N in (400, 800):
        for T in (6., 10.):
            h = T / N
            PN, diag = core.exact_law_3(Q, mu, N, h)
            print(f"-- {name}, N={N}, T={T}, T^2/N={T*T/N:.3f}, N/T^2={N/T/T:.1f}")
            print("     n3      x=h n3    alpha3     R_cont      R_lat")
            for n3 in (1, 2, 4, 8, 16, 32, 64, N // 8, N // 4):
                if (N - n3) % 2:
                    n3 += 1
                Np = N - n3
                n1 = n2 = Np // 2
                beta = [0.5, 0.5]
                cst = core.layer_constants(Q, G, i, beta)
                x, S = h * n3, h * Np
                PG = diag[Np][n1]
                kc = h * PG * core.bessel_kernel(cst["ab"], S, x, cst["gamma"])
                w = cst["ab"] * S * h / (1 - h * qi)
                kl = PG * np.exp(-cst["gamma2"] * x) * (1 - h * qi) ** n3 * core.laguerre_B(n3, w)
                print(f"   {n3:5d}   {x:8.4f}   {n3/N:7.4f}   {PN[n1, n2]/kc:9.6f}  {PN[n1, n2]/kl:9.6f}")
