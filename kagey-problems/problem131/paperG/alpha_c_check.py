"""The degenerate case alpha = alpha_c, b = 1, fair start.

Run with `py -I alpha_c_check.py [Nmax]`.  L_{alpha_c,1} has a single, degenerate, minimum
at 1/2 (L''(1/2) = 0 < L''''(1/2)).  We record, for two laws of index alpha_c, the bulk local
extrema of P_N: if a local maximum sits at N/2 between two minima at N/2 -+ w_N, the law is
W-shaped at that N although L is U-shaped.  We fit w_N against N.
"""
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from scipy.optimize import brentq
from shape_engine import Engine, sibuya, zeta_law, modes

if __name__ == "__main__":
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    ac = brentq(lambda a: math.cos(math.pi * a / 2) - a, 0.1, 0.9)
    for mk in (sibuya, zeta_law):
        L = mk(ac, Nmax + 5)
        E = Engine(L, L, Nmax)
        print("\n== %s, fair start, alpha_c = %.9f" % (L.name, ac))
        xs, ws = [], []
        for N in range(500, Nmax + 1, 250):
            P = E.fair(N)
            mx, mn, gap = modes(P)
            bulk_min = [a for a, b in mn if 0.05 * N < a < 0.95 * N]
            bulk_max = [a for a, b in mx if 0.05 * N < a < 0.95 * N]
            line = "  N=%5d modes=%d bulk maxima %s bulk minima %s" % (N, len(mx), bulk_max, bulk_min)
            if len(bulk_min) == 2:
                w = (bulk_min[1] - bulk_min[0]) / 2.0
                depth = (P[N // 2] - P[bulk_min[0]]) / P[N // 2]
                line += "  w_N=%.1f  w_N/N=%.4f  relative depth=%.2e" % (w, w / N, depth)
                xs.append(N)
                ws.append(w / N)
            print(line + "  gap %.1e" % gap)
        if len(xs) >= 3:
            slope = np.polyfit(np.log(xs), np.log(ws), 1)[0]
            print("  fit: w_N/N ~ N^%.3f" % slope)
        del E
