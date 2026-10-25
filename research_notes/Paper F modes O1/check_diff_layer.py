# check_diff_layer.py -- first and second differences of R_N(j)=P_N(N-j)/T_+(N)
# against Delta u + Delta C/N (fresh plus start, zeta laws).
# Paper F (problem 131), modal structure (O1).
# Run: py -I check_diff_layer.py
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from scipy.special import zeta as hz
from engine import zeta_law, layer_R, renewal, Cfun, sign_changes

alpha = 1.5
for N, J in ((1000, 80), (3000, 120), (10000, 200)):
    fp, Tp = zeta_law(alpha, N); fm, Tm = fp, Tp
    mu = hz(alpha, 1) / hz(alpha + 1, 1)
    R = layer_R(fp, Tp, fm, Tm, N, J)
    u = renewal(fm, J + 1)
    C = Cfun(alpha, mu, u, J + 1)
    dR = N * np.diff(R)                  # N (R(j+1)-R(j)), j = 0..J-1
    dM = N * np.diff(u[: J + 1]) + np.diff(C[: J + 1])
    scR = sign_changes(R)[0]
    scM = sign_changes(u[: J + 1] + C[: J + 1] / N)[0]
    print("N=%d  local min of R_N at j=%s ; of u+C/N at j=%s" % (N, scR, scM))
    for j in (1, 2, 5, 10, 20, 30, 40, 60, 80, 120, 160):
        if j < J:
            print("   j=%4d  N dR=%9.4f  N(du)+dC=%9.4f  diff=%8.4f" % (j, dR[j], dM[j], dR[j] - dM[j]))
    d2 = np.diff(dR)
    jstar = scR[0] if scR else None
    if jstar:
        w = d2[max(jstar - 10, 0): jstar + 10]
        print("   second differences N*D2R near j*: min %.3e max %.3e (all >0: %s)" % (w.min(), w.max(), bool((w > 0).all())))
        lo = 1
        neg = np.nonzero(d2[lo: 3 * jstar] <= 0)[0]
        print("   j in [1,3j*) with N*D2R <= 0:", (neg + lo)[:20])
