# o3_table.py -- exact face maxima of the four reducible faces E1-E4 (see
# 00_predictions.md): local log-slopes of N^(k_F-1) e^(T lambda_F) M_F in T, and the ratio
# M_F / (N^-(k_F-1) T^p e^(-T lambda_F)) against the predicted constant K.
# Run with: py -I o3_table.py [N]      (default N = 20000; about a minute per example)
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from o3_lib import face_max  # noqa: E402

N = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
L1 = (3 - math.sqrt(5)) / 2
CASES = {  # k_F, lambda_F, predicted power p, predicted K
    'E1': (3, 0.0, 1.5, 0.797885),
    'E2': (3, L1, 1.5, 0.260705),
    'E3': (4, L1, 2.5, 0.421830),
    'E4': (4, 1.0, 2.5, 0.398942),
}
Ts = [2, 3, 4, 6, 8, 11, 15, 20, 25]
print(f"N = {N}")
for ex, (kF, lam, p, K) in CASES.items():
    print(f"\n{ex}: k_F={kF}, lambda_F={lam:.6f}, predicted power {p}, predicted K {K}")
    print("     T   T^2/N    N^(k-1)e^(lT)M_F   local slope   M_F/X     (M_F/X)/K   extra")
    prev = None
    rows = []
    for T in Ts:
        r = face_max(ex, N, T)
        extra = ""
        if isinstance(r, tuple):
            r, l1 = r
            extra = f"C1 block time {l1 * T / N:.3f}"
        y = N ** (kF - 1) * math.exp(lam * T) * r
        slope = "" if prev is None else f"{(math.log(y) - math.log(prev[1])) / (math.log(T) - math.log(prev[0])):.4f}"
        ratio = y / T ** p
        print(f"  {T:4d}  {T * T / N:6.4f}  {y:16.6e}   {slope:>9s}   {ratio:.6f}  {ratio / K:.6f}   {extra}")
        prev = (T, y)
        rows.append((T, ratio))
    # least squares  ratio = c0 + c1/T + c2 T^2/N  over T >= 6
    sel = [(T, v) for T, v in rows if T >= 6]
    Amat = np.array([[1, 1 / T, T * T / N] for T, _ in sel])
    c = np.linalg.lstsq(Amat, np.array([v for _, v in sel]), rcond=None)[0]
    print(f"  fit over T>=6: ratio = {c[0]:.6f} + {c[1]:.4f}/T + {c[2]:.4f} T^2/N;"
          f" c0/K = {c[0] / K:.6f}")
