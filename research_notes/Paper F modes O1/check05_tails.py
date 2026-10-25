# check05_tails.py -- Lemma 12 of 05_report.md (tail sums of kernel
# differences): for the zeta law alpha = 3/2 prints
#   a(j/mu)^r * sum_{m not in I_j(K)} |Delta^r k_m(j)|,  r = 1, 2,
# for k = u_m and k = q_m, j = 250, 500, 1000 and K = 2, 4, 8, 16.
# The lemma predicts values bounded by C(K^(1-alpha+delta) + e^(-cK)) + o(1),
# so decreasing in K, and not growing in j.
# Paper F (problem 131), modal structure (O1).
# Run: py -I check05_tails.py   (under a minute)
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from scipy.special import zeta as hz
from exact04 import zeta_law

alpha = 1.5
J = 1003
f, T = zeta_law(alpha, J + 2)
mu = hz(alpha, 1) / hz(alpha + 1, 1)
cT = 1.0 / (alpha * hz(alpha + 1, 1))
a = lambda t: (cT * t) ** (1 / alpha)
fv = f[:J + 1].copy(); fv[0] = 0.0
U = np.zeros((J + 1, J + 1)); U[0, 0] = 1.0          # U[m, x] = f^{*m}(x)
for m in range(1, J + 1):
    U[m] = np.convolve(U[m - 1], fv)[:J + 1]
tau = T[:J + 1].copy(); tau[0] = 0.0                  # tau(v) = T(v), v >= 1
Q = np.zeros_like(U)                                  # Q[m] = q_m = u_{m-1} * tau
for m in range(1, J + 1):
    Q[m] = np.convolve(U[m - 1], tau)[:J + 1]
for name, Kn in (("u_m", U), ("q_m", Q)):
    for r in (1, 2):
        rows = []
        for j in (250, 500, 1000):
            A = a(j / mu)
            d = Kn[:, j + 1] - Kn[:, j] if r == 1 else Kn[:, j + 2] - 2 * Kn[:, j + 1] + Kn[:, j]
            m = np.arange(J + 1)
            vals = []
            for K in (2, 4, 8, 16):
                out = np.abs(j - m * mu) > K * A
                out[0] = True
                vals.append(A ** r * np.abs(d[out]).sum())
            rows.append("j=%4d: " % j + " ".join("%.4f" % v for v in vals))
        print("%s r=%d (K = 2, 4, 8, 16)   " % (name, r) + "   ".join(rows))
