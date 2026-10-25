# check_M1_starts.py -- Theorem M1 (first differences in the boundary layer)
# for fresh plus, fresh minus and fair starts, zeta law alpha = 3/2.
# Prints N(R_N(j+1)-R_N(j)) - [N Delta kappa(j) + Psi(j)] for several j, N.
# Paper F (problem 131), modal structure (O1).
# Run: py -I check_M1_starts.py
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from scipy.special import zeta as hz
from engine import zeta_law, layer_R_mixed, renewal

alpha = 1.5
mu = hz(alpha, 1) / hz(alpha + 1, 1)
Jmax = 200
f0, T0 = zeta_law(alpha, 50)
u = renewal(zeta_law(alpha, Jmax + 5)[0], Jmax + 2)
v = np.array([u[:j] @ u[j:0:-1] if j > 0 else 0.0 for j in range(Jmax + 3)])
du = np.diff(u); dv = np.diff(v)
jj = np.arange(len(du))
psi_plus = alpha * ((jj + 1) * du + 2 * mu * dv + 2 * u[:-1])
psi_minus = psi_plus - 2 * alpha * mu * du
for name, wp, wm in (("plus", 1.0, 0.0), ("minus", 0.0, 1.0), ("fair", 0.5, 0.5)):
    psi = wp * psi_plus + wm * psi_minus
    for N in (1000, 3000, 10000):
        J = min(Jmax, int(2 * N ** (2 / 3) / 4))
        f, T = zeta_law(alpha, N)
        R = layer_R_mixed(f, T, f, T, N, J, wp, wm)
        dR = N * np.diff(R)
        out = []
        for j in (1, 2, 5, 10, 20, 40, 80, 160):
            if j < J:
                out.append("j=%d: %.4f" % (j, dR[j] - (N * du[j] + psi[j])))
        print("%-5s N=%5d  %s" % (name, N, "  ".join(out)))
