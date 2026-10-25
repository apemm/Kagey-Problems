# check_du.py -- difference form of the renewal theorem:
# (u(j)-u(j-1)) mu^2 / T(j) -> -1 under (RV)+(SPAN)  (Lemma 1 of 01_report.md).
# Paper F (problem 131), modal structure (O1).
# Run: py -I check_du.py
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from engine import zeta_law, renewal

J = 20000
for alpha, nmin in ((1.2, 1), (1.5, 1), (1.8, 1), (1.5, 2)):
    f, T = zeta_law(alpha, J, nmin)
    mu = T[1:].sum() + (J + 1) * T[J + 1] / alpha  # sum_{m>=1} T(m), tail by integral
    # better: mu = sum n f(n) exactly via Hurwitz zeta
    from scipy.special import zeta as hz
    s = alpha + 1
    mu = hz(s - 1, nmin) / hz(s, nmin)
    u = renewal(f, J)
    du = np.diff(u)  # du[j-1] = u(j)-u(j-1)
    row = []
    for j in (10, 100, 1000, 5000, 20000):
        row.append("j=%d: %.4f" % (j, du[j - 1] * mu ** 2 / T[j]))
    last_pos = np.nonzero(du > 0)[0]
    lp = (last_pos[-1] + 1) if len(last_pos) else None
    print("alpha", alpha, "nmin", nmin, "| last j with u(j)>u(j-1):", lp, "|", ", ".join(row))
