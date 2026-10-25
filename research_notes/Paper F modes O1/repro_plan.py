# repro_plan.py -- independent reproduction of the O1 numerics of the plan
# (04_F_modes_numerics.md), with the exact recursion of engine.py.
# Paper F (problem 131), modal structure (O1).
# Run: py -I repro_plan.py  (about a few minutes; prints tables)
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from engine import zeta_law, law_from_f, build, law_N, renewal, sign_changes


def seeds(n, fair):
    S0 = np.zeros((n + 1, n + 1)); E0 = np.zeros((n + 1, n + 1))
    if fair:
        S0[0, 0] = 0.5; E0[0, 0] = 0.5
    else:
        S0[0, 0] = 1.0
    return S0, E0


def modified_zeta(alpha, nmax, mult2):
    f, T = zeta_law(alpha, nmax)
    g = f.copy(); g[2] *= mult2
    g /= (1.0 + (mult2 - 1.0) * f[2])
    return law_from_f(g)


def run_single():
    print("== 1. fair start, N = 2000: sign changes of Delta P_N ==")
    for ap, am in ((1.5, 1.5), (1.9, 1.3)):
        n = 2000
        fp, Tp = zeta_law(ap, n); fm, Tm = zeta_law(am, n)
        S, E = build(fp, fm, n, *seeds(n, True))
        P = law_N(S, E, Tp, Tm, n)
        sc, first = sign_changes(P)
        print(ap, am, "first sign", first, "changes at k =", sc)
        S, E = build(fp, fm, n, *seeds(n, False))
        P = law_N(S, E, Tp, Tm, n)
        sc, first = sign_changes(P)
        print(ap, am, "(fresh plus) first sign", first, "changes at k =", sc)


def run_scan():
    print("== 2. fair start, every N in 2..400 ==")
    for ap, am in ((1.2, 1.2), (1.5, 1.5), (1.8, 1.8), (1.9, 1.3), (1.3, 1.9)):
        n = 400
        fp, Tp = zeta_law(ap, n); fm, Tm = zeta_law(am, n)
        S, E = build(fp, fm, n, *seeds(n, True))
        counts = {}
        first5 = None
        after = set()
        for N in range(2, n + 1):
            P = law_N(S, E, Tp, Tm, N)
            c = len(sign_changes(P)[0])
            counts[c] = counts.get(c, 0) + 1
            if c == 5 and first5 is None:
                first5 = N
            if first5 is not None:
                after.add(c)
        print(ap, am, "counts seen", sorted(counts), "first N with 5:", first5,
              "counts after:", sorted(after))


def run_nonlc():
    print("== 3. runs >= 2 (alpha 1.5), fair start ==")
    n = 4000
    f, T = zeta_law(1.5, n, nmin=2)
    S, E = build(f, f, n, *seeds(n, True))
    for N in (100, 200, 500, 1000, 1500, 2000, 3000, 4000):
        P = law_N(S, E, T, T, N)
        sc, first = sign_changes(P)
        left = [k for k in sc if k < N / 2]
        print(N, "total", len(sc), "left side", len(left), "first", first)
        if N in (1000, 4000):
            d = np.diff(P)
            rel = [abs(d[k]) / P[k] for k in sc]
            print("   min, max |dP|/P at changes:", min(rel), max(rel))


def run_layer():
    print("== 4. fresh plus, N = 3000, layer j < N/3 ==")
    n = 3000
    laws = {
        "zeta": zeta_law(1.5, n),
        "f(2) x2": modified_zeta(1.5, n, 2.0),
        "f(2) x4": modified_zeta(1.5, n, 4.0),
        "runs>=2": zeta_law(1.5, n, nmin=2),
    }
    for name, (f, T) in laws.items():
        S, E = build(f, f, n, *seeds(n, False))
        P = law_N(S, E, T, T, n)
        R = P[::-1]  # R[j] = P_N(N-j)
        u = renewal(f, n // 3)
        scu, _ = sign_changes(u, 0, n // 3)
        scR, _ = sign_changes(R, 0, n // 3)
        print(name, "| u_- changes at", scu, "| P_N(N-j) changes at", scR)


if __name__ == "__main__":
    which = sys.argv[1:] or ["single", "scan", "nonlc", "layer"]
    for w in which:
        {"single": run_single, "scan": run_scan, "nonlc": run_nonlc,
         "layer": run_layer}[w]()
