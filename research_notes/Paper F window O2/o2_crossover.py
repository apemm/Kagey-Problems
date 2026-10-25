# o2_crossover.py
# Problem 131, Paper F, window O2: the crossover between the light-side
# deviation of the minus runs and the big jump of a plus run.
# Equal indices alpha, theta_+ made small by the plus law (1-w) delta_1 + w zeta.
# For each w: exact P_N, kernel G_N, finite-N light exponent Lambda~_N(k), the
# observed crossover x_c (first x > 1 with P_N <= 2 G_N) and the predicted
# x*_N solving Lambda~_N(k) = -log(B_N G_N(k)).
# Run: py -I o2_crossover.py N alpha w1 w2 ...
import os, sys, time, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from o2_lib import Law, Setup, exact_law, Lambda_tilde, stable_light_const

N = int(sys.argv[1]); alpha = float(sys.argv[2]); ws = [float(a) for a in sys.argv[3:]]
cZ, beta = stable_light_const(alpha)
print(f"N={N} alpha={alpha} beta={beta:.4f} c_Z={cZ:.5f}")
summary = []
for w in ws:
    t = time.time()
    lp, lm = Law(alpha, w), Law(alpha)
    P = exact_law(N, lp, lm)
    S = Setup(N, lp, lm)
    k0 = int(math.ceil(S.p * N + S.B))           # x >= 1
    k1 = min(N, int(S.p * N + 40 * S.B))
    ks = np.arange(k0, k1 + 1)
    G = np.array([S.G(k) for k in ks])
    xs = (ks - S.p * N) / S.B
    ratio = P[ks] / G
    ic = np.argmax(ratio <= 2.0) if np.any(ratio <= 2.0) else None
    xc = xs[ic] if ic is not None else float('nan')
    # predicted crossover: Lambda~ = -log(B G); scan the same grid (coarsely)
    xmax = 2.0 * (xc if not math.isnan(xc) else 5.0) + 3.0
    idx = [i for i in range(len(ks)) if xs[i] <= xmax]
    step = max(1, len(idx) // 80)
    xstar = float('nan'); rows = []; prev = None
    for i in idx[::step]:
        lt = Lambda_tilde(S, int(ks[i]))
        rhs = -math.log(S.B * G[i])
        light = P[ks[i]] - G[i]
        ll = -math.log(S.B * light) if light > 0 else float('nan')
        rows.append((xs[i], lt, rhs, ll, ratio[i]))
        if math.isnan(xstar) and lt >= rhs:
            if prev is None:
                xstar = xs[i]
            else:   # linear interpolation of lt - rhs
                x0, d0 = prev; d1 = lt - rhs
                xstar = x0 + (xs[i] - x0) * (-d0) / (d1 - d0)
        prev = (xs[i], lt - rhs)
    print(f"\nw={w} p={S.p:.4f} B_N={S.B:.2f} theta+={S.thp:.5f} log(1/theta+)={math.log(1/S.thp):.3f} "
          f"x_c={xc:.3f} x*={xstar:.3f} x_c/x*={xc/xstar:.3f} 1-sumP={1-P.sum():.1e} ({time.time()-t:.0f}s)")
    print("   x    Lam~_N  -log(BG)  -log(B(P-G))  ratio  P/G")
    for (x, lt, rhs, ll, r) in rows:
        if abs(x - round(x)) <= 0.5 * step / S.B + 1e-9:
            print(f"{x:6.2f} {lt:8.3f} {rhs:8.3f} {ll:10.3f} {ll/lt if lt>0 else float('nan'):7.3f} {r:8.3f}")
    summary.append((w, S.thp, xc, xstar))
print("\nsummary: w theta+ log(1/theta+) x_c x* x_c/x* x_c/log(1/theta+) x_c/(log(1/theta+))^(1/beta)")
for (w, th, xc, xs_) in summary:
    L = math.log(1 / th)
    print(f"{w:7.4f} {th:8.5f} {L:7.3f} {xc:7.3f} {xs_:7.3f} {xc/xs_:6.3f} {xc/L if L>0 else float('nan'):7.3f} "
          f"{xc/L**(1/beta) if L>0 else float('nan'):7.3f}")
