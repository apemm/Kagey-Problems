"""Triple-face check for Task 2: compare the best of the six faces without the full triple with the best
composition of full support (n_k >= 1) found by the capped dynamic programme (n_k <= L).
Usage: py -I 03_task2_triple.py CONFIG L N1 N2 ...   (tau indices 4 and 8 of the grid, two ordered pairs)"""
import os, sys, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
from importlib import import_module
from multiprocessing import Pool
sc = import_module("03_task2_scan")
core = import_module("03_core")


def job(a):
    name, L, N, ti, (i, j) = a
    Q, pi, mu, S, R, b, q = sc.build(name)
    H, tau0, U, M = core.design_constants(R, b)
    taus, deltas = sc.grids(R, U)
    tau = taus[ti]
    T = tau * np.log(N)
    k = 3 - i - j
    if T * q.max() >= 0.97 * N:
        return None
    profs = {}
    for (x, y) in itertools.combinations(range(3), 2):
        profs[(x, y)] = sc.pair_profile(Q, mu, x, y, N, T)
    cap = core.capped_logprobs(Q, mu, N, T, i, k, L)
    rows = []
    ni = np.arange(N + 2)[:, None]
    nk = np.arange(L + 2)[None, :]
    for d in deltas:
        v = {i: d, j: 0.0, k: -M}
        lead = core.leading_scores(S, [v[0], v[1], v[2]], tau)
        order = sorted(lead.items(), key=lambda kv: kv[1])
        win = order[0][0]
        gap = order[1][1] - order[0][1]
        ex = {(s,): core.log_single(Q, mu, s, N, T, v[s]) for s in range(3)}
        for (x, y), pr in profs.items():
            if pr is None:
                continue
            nas, lp = pr
            ex[(x, y)] = float((lp + T * (v[x] * nas + v[y] * (N - nas)) / N).max())
        best6 = max(ex.values())
        tot = cap + T * (d * ni + 0.0 * (N - ni - nk) - M * nk) / N
        tot[:, 0] = -np.inf
        tot[:, L + 1:] = -np.inf
        tot[N + 1:, :] = -np.inf
        tot[0, :] = -np.inf
        tot[(N - ni - nk) < 1] = -np.inf
        flat = np.argmax(tot)
        a_, b_ = np.unravel_index(flat, tot.shape)
        rows.append((float(d), win, float(gap), best6, float(tot[a_, b_]), int(b_)))
    return name, N, ti, tau, (i, j), rows


if __name__ == "__main__":
    name = sys.argv[1]
    L = int(sys.argv[2])
    Ns = [int(x) for x in sys.argv[3:]]
    jobs = [(name, L, N, ti, pr) for N in Ns for ti in (4, 8) for pr in ((1, 0), (2, 1))]
    with Pool(12) as p:
        out = p.map(job, jobs)
    print(f"config {name}, L={L}: per (N, tau, retained pair): minimum over the 13 deltas of [log best six-face - log best full-support composition with 1<=n_k<=L] among cells with leading gap>=0.5; argmax n_k")
    print("| N | tau | pair | min margin | delta at min | predicted winner at min | n_k* | any negative margin |")
    print("|---:|---:|---|---:|---:|---|---:|---|")
    for r in out:
        if r is None:
            continue
        nm, N, ti, tau, pr, rows = r
        rr = [x for x in rows if x[2] >= 0.5 and len(x[1]) < 3]
        if not rr:
            continue
        m = min(rr, key=lambda x: x[3] - x[4])
        neg = any(x[3] - x[4] < 0 for x in rr)
        print(f"| {N} | {tau:.3f} | ({pr[0]+1},{pr[1]+1}) | {m[3]-m[4]:.2f} | {m[0]:.2f} | {tuple(s+1 for s in m[1])} | {m[5]} | {neg} |")
