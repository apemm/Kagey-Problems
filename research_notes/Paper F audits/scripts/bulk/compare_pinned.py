import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sys
import numpy as np
import bulk_check as b
AP, AM = b.AP, b.AM
mup = b.zeta(AP)/b.zeta(AP+1); mum = b.zeta(AM)/b.zeta(AM+1); s = mup+mum; p = mup/s
for N in [1000, 2000, 4000]:
    f, T = b.law(AP, N+1); fm, Tm = b.law(AM, N+1)
    P = b.occupation(N, f, T, fm, Tm)
    bp, bm = b.a_asym(AP, N/s), b.a_asym(AM, N/s); BN = max(bp, bm); thm = bm/BN
    ks = np.arange(int(p*N-4*BN), int(p*N+4*BN)+1)[::3]
    x = (ks-p*N)/BN
    hN = np.array([b.h(xx, 1.0, thm, p) for xx in x])
    hP = np.array([b.h(xx, 1.0, 0.0, p) for xx in x])
    y = BN*P[ks]
    print(f"N={N} th-={thm:.3f}  sup|BP-h_N|={np.max(abs(y-hN)):.4f}  sup|BP-h_pin|={np.max(abs(y-hP)):.4f}  "
          f"L1grid|BP-h_N|={np.mean(abs(y-hN)):.4f}  L1grid|BP-h_pin|={np.mean(abs(y-hP)):.4f}")
