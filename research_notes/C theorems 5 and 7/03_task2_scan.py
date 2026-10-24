"""Task 2: adversarial scan of the onset inside the class.

For a configuration (pi, conductances, start mu) and a grid of the protected rectangle
|delta| <= 3R, 1/(4R) <= tau <= U, for each ordered retained pair (i,j) with field
v_i = delta, v_j = 0, v_k = -M, compare the leading-score winner (smallest Phi) with the exact
maximiser over the six faces {s}, {a,b}.  The full triple is checked separately
(03_task2_triple.py).  Cells whose leading-score gap (second-smallest minus smallest Phi) is
< g0 are excluded.  Pair profiles use a stride grid (about 0.15 sqrt(N/T)) plus the 30 compositions
at each end.

Usage: py -I 03_task2_scan.py CONFIG N1 N2 ...
"""
import os, sys, json, time, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
from importlib import import_module
from multiprocessing import Pool
core = import_module("03_core")

CONFIGS = {
    # name: (pi, conductance dict, mu)
    "base":      ([.25, .35, .40], {(0, 1): .45, (0, 2): .34, (1, 2): .37}, [.3, .3, .4]),
    "weak13_a":  ([.25, .35, .40], {(0, 1): .45, (0, 2): .10, (1, 2): .37}, [.3, .3, .4]),
    "weak13_b":  ([.25, .35, .40], {(0, 1): .45, (0, 2): .03, (1, 2): .37}, [.3, .3, .4]),
    "weak13_c":  ([.25, .35, .40], {(0, 1): .45, (0, 2): .01, (1, 2): .37}, [.3, .3, .4]),
    "path":      ([.25, .35, .40], {(0, 1): .45, (1, 2): .37}, [.3, .3, .4]),
    "unequal_a": ([.80, .15, .05], {(0, 1): .30, (0, 2): .10, (1, 2): .08}, [.3, .3, .4]),
    "unequal_b": ([.90, .09, .01], {(0, 1): .30, (0, 2): .06, (1, 2): .02}, [.3, .3, .4]),
    "start_a":   ([.25, .35, .40], {(0, 1): .45, (0, 2): .34, (1, 2): .37}, [.90, .05, .05]),
    "start_b":   ([.25, .35, .40], {(0, 1): .45, (0, 2): .34, (1, 2): .37}, [.98, .01, .01]),
    "start_c":   ([.25, .35, .40], {(0, 1): .45, (0, 2): .34, (1, 2): .37}, [.998, .001, .001]),
    "unequal_start": ([.90, .09, .01], {(0, 1): .30, (0, 2): .06, (1, 2): .02}, [.02, .49, .49]),
}


def build(name):
    pi, cd, mu = CONFIGS[name]
    pi = np.array(pi, float)
    c = np.zeros((3, 3))
    for (a, b), x in cd.items():
        c[a, b] = c[b, a] = x
    Q = core.reversible_generator(pi, c)
    S, R, b, q, w = core.class_data(Q, pi)
    return Q, pi, np.array(mu, float), S, R, b, q


def grids(R, U):
    taus = np.geomspace(1 / (4 * R), U, 9)
    deltas = np.linspace(-3 * R, 3 * R, 13)
    return taus, deltas


def pair_profile(Q, mu, a, b, N, T):
    qm = max(Q[a, b], Q[b, a])
    if Q[a, b] * Q[b, a] == 0:
        return None
    s = max(1, int(0.15 * np.sqrt(N / max(T, 1.0))))
    nas = np.unique(np.concatenate([np.arange(1, N, s), np.arange(1, min(31, N)), np.arange(max(1, N - 30), N)]))
    nas, lp = core.log_pair_array(Q, mu, a, b, N, T, nas=nas)
    return nas, lp


def run_tau(args):
    name, N, ti = args
    Q, pi, mu, S, R, b, q = build(name)
    H, tau0, U, M = core.design_constants(R, b)
    taus, deltas = grids(R, U)
    tau = taus[ti]
    T = tau * np.log(N)
    if T * q.max() >= 0.97 * N:
        return dict(name=name, N=N, ti=ti, tau=tau, admissible=False)
    cost = 0.0
    for (a, bb) in itertools.combinations(range(3), 2):
        if Q[a, bb] * Q[bb, a] > 0:
            st = max(1, int(0.15 * np.sqrt(N / max(T, 1.0))))
            cost = max(cost, core.runs_K(Q, a, bb, N, T) * (N / st + 60))
    if cost > 4e8:
        return dict(name=name, N=N, ti=ti, tau=float(tau), admissible=True, skipped=True, cells=[])
    profs = {}
    for (a, bb) in itertools.combinations(range(3), 2):
        profs[(a, bb)] = pair_profile(Q, mu, a, bb, N, T)
    cells = []
    for (i, j) in itertools.permutations(range(3), 2):
        k = 3 - i - j
        for d in deltas:
            v = {i: d, j: 0.0, k: -M}
            vv = [v[0], v[1], v[2]]
            lead = core.leading_scores(S, vv, tau)
            order = sorted(lead.items(), key=lambda kv: kv[1])
            win, gap = order[0][0], order[1][1] - order[0][1]
            if len(win) == 3:
                continue
            ex = {}
            for s in range(3):
                ex[(s,)] = core.log_single(Q, mu, s, N, T, v[s])
            for (a, bb), pr in profs.items():
                if pr is None:
                    continue
                nas, lp = pr
                tot = lp + T * (v[a] * nas + v[bb] * (N - nas)) / N
                ex[(a, bb)] = float(tot.max())
            ewin = max(ex, key=ex.get)
            srt = sorted(ex.values(), reverse=True)
            cells.append(dict(i=i, j=j, delta=float(d), pred=list(win), gap=float(gap), exact=list(ewin),
                              exgap=float(srt[0] - srt[1])))
    return dict(name=name, N=N, ti=ti, tau=float(tau), admissible=True, cells=cells)


if __name__ == "__main__":
    name = sys.argv[1]
    Ns = [int(x) for x in sys.argv[2:]]
    Q, pi, mu, S, R, b, q = build(name)
    H, tau0, U, M = core.design_constants(R, b)
    jobs = [(name, N, ti) for N in Ns for ti in range(9)]
    out = os.path.join(HERE, f"03_task2_{name}.json")
    store = dict(name=name, R=R, b=b, U=U, M=M, q=list(q), mu=list(mu), pi=list(pi), results=[])
    t0 = time.time()
    with Pool(9) as pool:
        for r in pool.imap_unordered(run_tau, jobs):
            store["results"].append(r)
            print(name, r["N"], r["ti"], round(time.time() - t0), flush=True)
    json.dump(store, open(out, "w"), default=float)
