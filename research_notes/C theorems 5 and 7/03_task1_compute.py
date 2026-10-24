"""Task 1: exact finite-N pair-entry times t_{ij,N} and singleton switches x_{i,N}.

Generator (3 states, reversible): pi = (0.25, 0.35, 0.40), conductances
c12 = .45, c13 = .34, c23 = .37.  Start mu = (0.3, 0.3, 0.4).
States are labelled 0,1,2 here (1,2,3 in the note).  Reference state for the exit
differences d_i = q_i - q_0 is state 0.

Usage: py -I 03_task1_compute.py  N1 N2 ...   (appends to 03_task1_results.json)
"""
import os, sys, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
from importlib import import_module
from scipy.optimize import brentq
from multiprocessing import Pool
core = import_module("03_core")

pi = np.array([0.25, 0.35, 0.40])
c = np.array([[0, .45, .34], [.45, 0, .37], [.34, .37, 0]])
MU = np.array([0.3, 0.3, 0.4])
Q = core.reversible_generator(pi, c)
S, R, b, q, w = core.class_data(Q, pi)
H, tau0, U, M = core.design_constants(R, b)
PAIRS = [(i, j) for i in range(3) for j in range(3) if i != j]
if os.environ.get("T1_PAIRS"):  # e.g. T1_PAIRS=01,10 restricts the ordered pairs (0-based)
    PAIRS = [(int(x[0]), int(x[1])) for x in os.environ["T1_PAIRS"].split(",")]


def faces_exact(i, j, N, tau, delta):
    """exact log-max for the six faces without the full triple, field v_i=delta, v_j=0, v_k=-M."""
    k = 3 - i - j
    T = tau * np.log(N)
    v = {i: delta, j: 0.0, k: -M}
    out = {}
    for s in range(3):
        out[(s,)] = core.log_single(Q, MU, s, N, T, v[s])
    for (a, bb) in [(i, j), (i, k), (j, k)]:
        val, ns = core.best_pair_fast(Q, MU, a, bb, N, T, v[a], v[bb])
        out[tuple(sorted((a, bb)))] = val
    return out


def g_pair(i, j, N, tau):
    T = tau * np.log(N)
    si = core.log_single(Q, MU, i, N, T, H)
    sj = core.log_single(Q, MU, j, N, T, 0.0)
    val, _ = core.best_pair_fast(Q, MU, i, j, N, T, H, 0.0)
    return val - max(si, sj)


def stochastic_cap(i, j, N):
    # T * max exit rate of the pair < 0.97 N
    qm = max(q[i], q[j])
    return 0.97 * N / (qm * np.log(N))


def task(args):
    i, j, N = args
    t0 = time.time()
    t = core.limit_t_ij(Q, i, j, H)
    cap = stochastic_cap(i, j, N)
    hi = min(1.25 * t, cap)
    lo = 0.25 * t
    taus = np.linspace(lo, hi, 18)
    g = [g_pair(i, j, N, x) for x in taus]
    signs = [np.sign(x) for x in g]
    changes = [m for m in range(len(g) - 1) if signs[m] < 0 <= signs[m + 1]]
    down = [m for m in range(len(g) - 1) if signs[m] >= 0 > signs[m + 1]]
    res = dict(i=i, j=j, N=N, t=t, cap=cap, n_up=len(changes), n_down=len(down))
    if not changes:
        res["tauN"] = None
        res["note"] = "no crossing in [%.3f,%.3f]" % (lo, hi)
        res["g"] = g
        return res
    m = changes[0]
    tauN = brentq(lambda x: g_pair(i, j, N, x), taus[m], taus[m + 1], xtol=1e-11, rtol=1e-13)
    res["tauN"] = tauN
    # winners just below / above, six faces
    eps = 1e-3 * t
    for tag, x in (("below", tauN - eps), ("above", tauN + eps)):
        f = faces_exact(i, j, N, x, H)
        order = sorted(f.items(), key=lambda kv: -kv[1])
        res["win_" + tag] = [list(order[0][0]), order[0][1], list(order[1][0]), order[1][1]]
    res["time"] = time.time() - t0
    return res


def switch_task(args):
    """singleton switch x_{i,N} at tau0 for the retained pair (i, 0)."""
    i, N = args
    T = tau0 * np.log(N)
    # exact singleton crossing: mu_0 (1-T q_0/N)^(N-1) = mu_i (1-T q_i/N)^(N-1) e^{T delta}
    lg = lambda s: (N - 1) * np.log(1 - T * q[s] / N)
    dN = (lg(0) - lg(i) + np.log(MU[0] / MU[i])) / T
    xi = q[i] - q[0]
    res = dict(i=i, N=N, xN=dN, x=xi)
    # exact competition of all six faces over a window of delta around dN
    k = 3 - i - 0
    cache_pair = {}
    deltas = np.linspace(dN - 0.3, dN + 0.3, 601)
    win = []
    margin_pair = []
    vals_cache = {}
    # pair arrays do not depend on delta; compute once
    arrs = {}
    for (a, bb) in [(0, i), (0, k), (i, k)]:
        nas, lp = (core.log_pair_array(Q, MU, a, bb, N, T) if N <= 6000 else (None, None))
        arrs[(a, bb)] = (nas, lp)
    if N > 6000:
        res["note"] = "pair arrays skipped for N>6000; margin computed with fast maximiser at dN only"
        v = {i: dN, 0: 0.0, k: -M}
        f = {}
        for s in range(3):
            f[(s,)] = core.log_single(Q, MU, s, N, T, v[s])
        for (a, bb) in [(0, i), (0, k), (i, k)]:
            val, _ = core.best_pair_fast(Q, MU, a, bb, N, T, v[a], v[bb])
            f[tuple(sorted((a, bb)))] = val
        order = sorted(f.items(), key=lambda kv: -kv[1])
        res["at_dN_top"] = [list(order[0][0]), order[0][1], list(order[1][0]), order[1][1], list(order[2][0]), order[2][1]]
        res["pair_margin_at_dN"] = f[(0,)] - f[tuple(sorted((0, i)))]
        return res
    seq = []
    for d in deltas:
        v = {i: d, 0: 0.0, k: -M}
        f = {}
        for s in range(3):
            f[(s,)] = core.log_single(Q, MU, s, N, T, v[s])
        for (a, bb), (nas, lp) in arrs.items():
            tot = lp + T * (v[a] * nas + v[bb] * (N - nas)) / N
            f[tuple(sorted((a, bb)))] = tot.max()
        wkey = max(f, key=f.get)
        seq.append(wkey)
        if abs(d - dN) < 1e-9 or True:
            margin_pair.append(f[tuple(sorted((0, i)))] - max(f[(0,)], f[(i,)]))
    # transitions
    trans = [(float(deltas[m]), seq[m], seq[m + 1]) for m in range(len(seq) - 1) if seq[m] != seq[m + 1]]
    res["transitions"] = [[a, list(b), list(cc)] for a, b, cc in trans]
    res["max_pair_margin_over_window"] = float(max(margin_pair))
    return res


if __name__ == "__main__":
    Ns = [int(x) for x in sys.argv[1:]]
    out_path = os.path.join(HERE, "03_task1_results.json")
    store = json.load(open(out_path)) if os.path.exists(out_path) else {"pair": [], "switch": []}
    jobs = [(i, j, N) for N in Ns for (i, j) in PAIRS]
    sj = [(i, N) for N in Ns for i in (1, 2)] if not os.environ.get("T1_PAIRS") else []
    with Pool(min(22, len(jobs))) as pool:
        for r in pool.imap_unordered(task, jobs):
            store["pair"].append(r)
            print("pair", r["i"], r["j"], r["N"], r.get("tauN"), r["t"], r.get("time"), flush=True)
        for r in pool.imap_unordered(switch_task, sj):
            store["switch"].append(r)
            print("switch", r["i"], r["N"], r["xN"], r["x"], flush=True)
    json.dump(store, open(out_path, "w"), default=float, indent=0)
