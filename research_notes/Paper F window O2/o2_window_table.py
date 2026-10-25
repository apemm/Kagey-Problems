# o2_window_table.py
# Problem 131, Paper F, window O2: the plan's table, recomputed independently.
# Zeta run laws alpha_+ = 1.9, alpha_- = 1.3 (plus scale smaller), fresh plus
# start. Ratios of the exact P_N(k) to h_N/B_N, G_N, h_N/B_N + G_N and the
# composite h_N/B_N + G_N - tau_N/B_N, plus the light-side exponent.
# Run: py -I o2_window_table.py 2000 5000
import os, sys, time, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from o2_lib import Law, Setup, exact_law, stable_light_const, Lambda_tilde

lp, lm = Law(1.9), Law(1.3)
cZ, beta = stable_light_const(lm.alpha)
for N in [int(a) for a in sys.argv[1:]]:
    t = time.time()
    P = exact_law(N, lp, lm)
    S = Setup(N, lp, lm)
    print(f"N={N} p={S.p:.5f} B_N={S.B:.2f} b+={S.bp:.2f} theta+={S.thp:.4f} "
          f"lambda_N={1+math.log(1/S.thp):.3f} 1-sumP={1-P.sum():.1e} ({time.time()-t:.1f}s)")
    print(" x      k    P/bulk  P/G    P/sum  P/comp  Lam_N   Lam~_N  cZ(x/p)^b  -log(B(P-G))")
    for x in [1, 2, 3, 4, 6, 8, 10, 15, 20]:
        k = int(round(S.p * N + x * S.B))
        if k > N:
            continue
        xx = S.x_of(k)
        h = S.h(xx) / S.B
        G = S.G(k)
        tau = S.tau(xx) / S.B
        comp = h + G - tau
        lam = S.LambdaN(xx)
        lt = Lambda_tilde(S, k)
        light = P[k] - G
        ll = -math.log(S.B * light) if light > 0 else float('nan')
        print(f"{xx:5.2f} {k:6d} {P[k]/h:6.3f} {P[k]/G:7.3f} {P[k]/(h+G):6.3f} "
              f"{P[k]/comp:6.3f} {lam:7.3f} {lt:7.3f} {cZ*(xx/S.p)**beta:9.3f} {ll:9.3f}")
