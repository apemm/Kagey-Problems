# inspect_cm.py -- details of the fresh-plus cases with 6 sign changes found by
# check_cm_everyN.py (completely monotone geometric mixtures).
# Paper F (problem 131), modal structure (O1).
# Run: py -I inspect_cm.py
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from engine import build, law_N, sign_changes
from check_cm_everyN import geo_mix
for ws, ths, N in (([.9, .1], [.1, .99], 186), ([.5, .5], [.3, .97], 131)):
    f, T = geo_mix(ws, ths, N)
    S0 = np.zeros((N + 1, N + 1)); S0[0, 0] = 1.0
    S, E = build(f, f, N, S0, None)
    P = law_N(S, E, T, T, N)
    sc, first = sign_changes(P)
    print(ws, ths, "N", N, "first sign", first, "changes", sc)
    for k in sc:
        print("   k=%d P=%.3e  rel dP before/after: %.2e %.2e" % (k, P[k], (P[k]-P[k-1])/P[k], (P[k+1]-P[k])/P[k]))
    lm = [k for k in range(N+1) if (k == 0 or P[k] > P[k-1]) and (k == N or P[k] >= P[k+1]) and P[k] > 0]
    print("   local maxima at", lm)
