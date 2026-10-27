"""Every-N counts for Sibuya run laws (heavy-tailed completely monotone laws, 0 < alpha < 1).

Run with `py -I cm_sibuya_everyN.py [Nmax]`.  For each pair (alpha_+, alpha_-) on a grid and
every 2 <= N <= Nmax we record the total and interior mode counts for the fair start and both
fresh starts, and compare with the eventual counts of the classification
(fresh: 2 + m_L total, fair: 2 + m_L total; m_L only when alpha_+ = alpha_-; for unequal
indices the eventual count is 2 + m_h).  Output: the maximum over N of each count.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from shape_engine import Engine, sibuya, modes

if __name__ == "__main__":
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 800
    grid = (0.1, 0.3, 0.5, 0.6, 0.7, 0.8, 0.9, 0.97)
    print("Nmax=%d. columns: alpha_+ alpha_-  | max total modes over N (fair, plus, minus)"
          " | max interior modes (fair, plus, minus) | N attaining the fair max" % Nmax)
    overall = {}
    for ap in grid:
        for am in grid:
            if am < ap:
                continue
            E = Engine(sibuya(ap, Nmax + 5), sibuya(am, Nmax + 5), Nmax)
            mt = {"fair": (0, 0), "plus": (0, 0), "minus": (0, 0)}
            mi = {"fair": 0, "plus": 0, "minus": 0}
            for N in range(2, Nmax + 1):
                for st in ("fair", "plus", "minus"):
                    P = E.fair(N) if st == "fair" else E.fresh(N, 1 if st == "plus" else -1)
                    mx, _, _ = modes(P, rtol=1e-11)
                    t = len(mx)
                    i = len([1 for a, b in mx if a > 0 and b < N])
                    if t > mt[st][0]:
                        mt[st] = (t, N)
                    mi[st] = max(mi[st], i)
            print("  %.2f %.2f | %d %d %d | %d %d %d | %d"
                  % (ap, am, mt["fair"][0], mt["plus"][0], mt["minus"][0],
                     mi["fair"], mi["plus"], mi["minus"], mt["fair"][1]))
            for k in mt:
                overall[k] = max(overall.get(k, 0), mt[k][0])
            del E
    print("overall maxima of total modes:", overall)
