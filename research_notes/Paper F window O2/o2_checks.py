# o2_checks.py
# Problem 131, Paper F, window O2: exactness checks of the recursion in o2_lib.
# (1) brute-force enumeration of run sequences for N <= 12;
# (2) independent forward Markov recursion on (count, sign, age) at N = 300;
# (3) total mass at N = 2000.
# Run: py -I o2_checks.py
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from o2_lib import Law, exact_law, brute_law, markov_law

laws = [(Law(1.9), Law(1.3)), (Law(1.8, 0.01), Law(1.8)), (Law(1.5, 0.3), Law(1.2, 0.7))]
worst = 0.0
for lp, lm in laws:
    for N in range(1, 13):
        d = np.max(np.abs(exact_law(N, lp, lm) - brute_law(N, lp, lm)))
        worst = max(worst, d)
print(f"brute force N<=12, three law pairs: max abs diff {worst:.2e}")

for lp, lm in laws:
    t = time.time()
    a, b = exact_law(300, lp, lm), markov_law(300, lp, lm)
    print(f"N=300 alpha=({lp.alpha},{lm.alpha}) w=({lp.w},{lm.w}): max abs diff "
          f"{np.max(np.abs(a-b)):.2e}, max rel diff (P>1e-12) "
          f"{np.max(np.abs(a-b)[a>1e-12]/a[a>1e-12]):.2e}  ({time.time()-t:.1f}s)")

t = time.time()
P = exact_law(2000, Law(1.9), Law(1.3))
print(f"N=2000 zeta(1.9,1.3): 1 - sum P = {1-P.sum():.2e}, min P = {P.min():.2e} ({time.time()-t:.1f}s)")
