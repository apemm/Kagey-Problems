# o2_exact_checks.py -- P1: the exact law three ways (forward recursion, Good's run
# sum, brute force) for the two-state chain, and recursion vs brute force on three states.
# Run with: py -I o2_exact_checks.py
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from o2_lib import (dp_two_state_log, good_two_state_log, brute_log,  # noqa: E402
                    dp_three_state_log)

A = [[0, 1], [2, 0]]
q = [1, 2]
for mu in ([0.5, 0.5], [2 / 3, 1 / 3]):
    # brute force, small N
    worst = 0.0
    for N in (5, 9, 14):
        for h in (0.1, 0.3):
            B = brute_log(N, h, A, q, mu)
            L = dp_two_state_log(N, h, A, q, mu)
            for (c0, c1), v in B.items():
                worst = max(worst, abs(L[c0] - v))
                if 0 < c0 < N:
                    worst = max(worst, abs(good_two_state_log(N, c0, h, A, q, mu) - v))
    print(f"mu={mu}: max |log diff| recursion/Good vs brute force, N<=14: {worst:.1e}")
    # N = 4000: recursion vs Good on every interior n
    N = 4000
    for T in (16, 400):
        h = T / N
        L = dp_two_state_log(N, h, A, q, mu)
        d = max(abs(L[n1] - good_two_state_log(N, n1, h, A, q, mu)) for n1 in range(1, N, 7))
        tot = np.logaddexp.reduce(L)
        print(f"  N=4000 T={T}: max |log diff| recursion vs Good (every 7th n): {d:.1e};"
              f"  log total mass {tot:.1e}")

# three states, killed and conservative
A3 = [[0, 2, 0.7], [0.5, 0, 1], [1.5, 0.3, 0]]
q3 = [2.7, 1.5, 1.8]
mu3 = [0.5, 0.3, 0.2]
worst = 0.0
for N in (6, 9):
    for h in (0.1, 0.25):
        B = brute_log(N, h, A3, q3, mu3)
        L = dp_three_state_log(N, h, A3, q3, mu3)
        for (c0, c1, c2), v in B.items():
            worst = max(worst, abs(L[c0, c1] - v))
print(f"three states: max |log diff| recursion vs brute force, N<=9: {worst:.1e}")
L = dp_three_state_log(200, 0.1, A3, q3, mu3)
print(f"three states N=200: log total mass {np.logaddexp.reduce(L[np.isfinite(L)]):.1e}")
