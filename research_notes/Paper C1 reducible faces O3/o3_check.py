# o3_check.py -- (1) block engine against brute force for small N, (2) predicted
# constants from Definition def:tilt, (3) the two continuum sups of example E4.
# Run with: py -I o3_check.py
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from o3_lib import face_max, brute_face_max, predicted_constant, besseli_series  # noqa: E402

print("(1) engine vs brute force: max relative difference of M_F")
for ex in ('E1', 'E2', 'E3', 'E4'):
    worst = 0.0
    for N in (8, 13, 21, 30):
        for T in (0.7, 2.0, 3.5):
            if T / N * 3 > 0.5:
                continue
            a = face_max(ex, N, T)
            a = a[0] if isinstance(a, tuple) else a
            b = brute_face_max(ex, N, T)
            worst = max(worst, abs(a - b) / b)
    print(f"  {ex}: {worst:.2e}")

print("(2) predicted constants (Definition def:tilt)")
s2pi = math.sqrt(2 * math.pi)
lam, al, K = predicted_constant([[-1, 1], [1, -1]], [1, 0], [1, 1])
print(f"  E1: lambda_C={lam:.6f} alpha*={al.round(6)} K={K:.6f}"
      f"  (sqrt(2/pi)={math.sqrt(2 / math.pi):.6f})")
lam, al, K = predicted_constant([[-2, 1], [1, -1]], [1, 0], [1, 0])
print(f"  E2: lambda_C={lam:.6f} alpha*={al.round(6)} K={K:.6f}"
      "  (start 1, end weight l_1, times q13=1)")
lam, al, K = predicted_constant([[-1, 1], [1, -2]], [1, 0], [0, 1])
print(f"  E3: lambda_C={lam:.6f} alpha*={al.round(6)} K={K:.6f}"
      "  (start 2 via q12=1, end 3 via q34=1)")
lam, al, K1 = predicted_constant([[-2, 1], [1, -2]], [1, 0], [1, 0])
print(f"  E4, j*=1, before the factor B_1/l_1: K={K1:.6f}")

print("(3) E4 continuum sups")
best_b, arg_b = 0.0, None
best_a, arg_a = 0.0, None
grid = [i * 0.04 for i in range(1, 301)]
for t1 in grid:
    for t2 in grid:
        x = 2 * math.sqrt(t1 * t2)
        u = math.sqrt(t1 / t2)
        e = math.exp(-t1 - t2)
        fb = e * (besseli_series(0, x) + u * besseli_series(1, x))
        fa = e * u * besseli_series(1, x)
        if fb > best_b:
            best_b, arg_b = fb, (t1, t2)
        if fa > best_a:
            best_a, arg_a = fa, (t1, t2)
print(f"  sup e^(-s) H_(3,free) on grid: {best_b:.6f} at {arg_b}  (limit 1 as s->0)")
print(f"  A_2 = sup e^(-s) H_(1->1) on grid: {best_a:.6f} at {arg_a}")
fa0 = max(t * math.exp(-t) for t in [0.8 + i * 0.001 for i in range(401)])
print(f"  boundary t2->0: max t1 e^-t1 = {fa0:.6f} (1/e = {1 / math.e:.6f})")
K1 = 0.5 / (s2pi / 2)
K2 = max(best_a, fa0) / (s2pi / 2)
print(f"  K_1 = {K1:.6f}, K_2 = {K2:.6f}, predicted K_E4 = {max(K1, K2):.6f}")
