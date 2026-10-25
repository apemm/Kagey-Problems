# o2_smoke.py -- quick consistency checks of o2_lib (rate, both constants, continuum limit).
# Run with: py -I o2_smoke.py
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from o2_lib import rate, constant_hessian_route, constant_torus_route  # noqa: E402

A = [[0, 1], [2, 0]]
q = [1, 2]
mu = [0.5, 0.5]
print("J_0(2/3,1/3) =", rate([2 / 3, 1 / 3], 0, A, q)[0], "(0 expected)")
print("J_0(1/2,1/2) =", rate([0.5, 0.5], 0, A, q)[0],
      "closed form", (math.sqrt(0.5) - math.sqrt(1.0)) ** 2)
for h in (0.0, 0.05, 0.25):
    for a in (0.5, 0.6, 0.8):
        C1 = constant_hessian_route([a, 1 - a], h, A, q, mu)
        C2, grad, gerr = constant_torus_route([a, 1 - a], h, A, q, mu)
        print(f"h={h:5.2f} a={a:4.2f}  C(hess)={C1:.10f}  C(torus)={C2:.10f}  "
              f"rel diff={abs(C1 / C2 - 1):.1e}  |grad|={abs(grad).max():.1e}  |g-th1|={gerr:.1e}")
