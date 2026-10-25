# check_cm_everyN.py -- bounded look at "at most three modes for every N" for
# completely monotone run laws: mixtures of geometric laws, and zeta laws.
# Counts sign changes of Delta P_N for every N <= NMAX (fair and fresh plus).
# Paper F (problem 131), modal structure (O1).
# Run: py -I check_cm_everyN.py
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from engine import zeta_law, build, law_N, sign_changes

NMAX = 300


def geo_mix(ws, ths, nmax):
    n = np.arange(nmax + 2, dtype=float)
    f = np.zeros(nmax + 2); T = np.zeros(nmax + 2)
    for w, th in zip(ws, ths):
        f[1:] += w * (1 - th) * th ** (n[1:] - 1)
        T[1:] += w * th ** (n[1:] - 1)
    T[0] = 1.0
    return f, T

laws = {
    "geo .9@.1 + .1@.99": geo_mix([.9, .1], [.1, .99], NMAX),
    "geo .5@.3 + .5@.97": geo_mix([.5, .5], [.3, .97], NMAX),
    "geo .98@.05 + .02@.999": geo_mix([.98, .02], [.05, .999], NMAX),
    "geo 3 atoms .6@.2,.3@.9,.1@.995": geo_mix([.6, .3, .1], [.2, .9, .995], NMAX),
    "single geo .95": geo_mix([1.0], [.95], NMAX),
    "zeta 1.1": zeta_law(1.1, NMAX),
}
names = list(laws)
pairs = [(a, a) for a in names] + [(names[0], names[1]), (names[2], names[5]), (names[3], names[4])]
if __name__ != "__main__":
    pairs = []
for a, b in pairs:
    fp, Tp = laws[a]; fm, Tm = laws[b]
    for start in ("fair", "plus"):
        S0 = np.zeros((NMAX + 1, NMAX + 1)); E0 = np.zeros((NMAX + 1, NMAX + 1))
        if start == "fair":
            S0[0, 0] = .5; E0[0, 0] = .5
        else:
            S0[0, 0] = 1.0
        S, E = build(fp, fm, NMAX, S0, E0)
        worst, worstN = -1, None
        seen = set()
        for N in range(2, NMAX + 1):
            c = len(sign_changes(law_N(S, E, Tp, Tm, N))[0])
            seen.add(c)
            if c > worst:
                worst, worstN = c, N
        print("%-34s | %-34s | %-4s counts %s, max %d first at N=%s" % (a, b, start, sorted(seen), worst, worstN))
