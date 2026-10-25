# check_engine.py -- validates engine.py against a brute-force Markov DP.
# Paper F (problem 131), modal structure (O1).
# Run: py -I check_engine.py
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from engine import zeta_law, build, law_N

def brute(fp, Tp, fm, Tm, N, start):
    # state: (k plus so far, sign of current run, age a of current run)
    # hazard of ending after age a: f(a)/T(a)
    from collections import defaultdict
    cur = defaultdict(float)
    cur[(1 if start > 0 else 0, start, 1)] = 1.0
    for n in range(1, N):
        nxt = defaultdict(float)
        for (k, s, a), p in cur.items():
            f, T = (fp, Tp) if s > 0 else (fm, Tm)
            h = f[a] / T[a]  # P(run length = a | length >= a)
            # continue
            nxt[(k + (1 if s > 0 else 0), s, a + 1)] += p * (1 - h)
            # switch
            ns = -s
            nxt[(k + (1 if ns > 0 else 0), ns, 1)] += p * h
        cur = nxt
    P = np.zeros(N + 1)
    for (k, s, a), p in cur.items():
        P[k] += p
    return P

fp, Tp = zeta_law(1.5, 60)
fm, Tm = zeta_law(1.3, 60, nmin=2)
S, E = build(fp, fm, 40, S0=np.pad([[1.0]], ((0, 40), (0, 40))))
for N in (5, 17, 40):
    a = law_N(S, E, Tp, Tm, N)
    b = brute(fp, Tp, fm, Tm, N, +1)
    print(N, abs(a - b).max(), a.sum())
