"""Task 2, triple face with one visit to the suppressed state.  For each (config, N, tau) and every ordered retained
pair and delta of the grid, margin = log(best of the six faces without the full triple) - log(best composition with
n_k = 1) (exact formula n1_profile, validated against the dynamic programme in 03_validate_n1.py).
Reports the minimum margin over cells with leading gap >= 0.5.
Usage: py -I 03_task2_n1.py CONFIG N1 N2 ..."""
import os, sys, json, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
from importlib import import_module
from multiprocessing import Pool
sc = import_module("03_task2_scan")
core = import_module("03_core")


def job(a):
    name, N, ti = a
    Q, pi, mu, S, R, b, q = sc.build(name)
    H, tau0, U, M = core.design_constants(R, b)
    taus, deltas = sc.grids(R, U)
    tau = taus[ti]
    T = tau * np.log(N)
    if T * q.max() >= 0.97 * N:
        return dict(name=name, N=N, ti=ti, tau=float(tau), status="inadmissible")
    cost = 0.0
    for (x, y) in itertools.combinations(range(3), 2):
        if Q[x, y] * Q[y, x] > 0:
            st = max(1, int(0.15 * np.sqrt(N / max(T, 1.0))))
            cost = max(cost, core.runs_K(Q, x, y, N, T) * (N / st + 60))
    if cost > float(os.environ.get('N1_COST', 1.5e9)):
        return dict(name=name, N=N, ti=ti, tau=float(tau), status="skipped")
    profs, n1 = {}, {}
    for (x, y) in itertools.combinations(range(3), 2):
        profs[(x, y)] = sc.pair_profile(Q, mu, x, y, N, T)
        if profs[(x, y)] is not None:
            k = 3 - x - y
            s = max(1, int(0.15 * np.sqrt(N / max(T, 1.0))))
            nas = np.unique(np.concatenate([np.arange(1, N - 1, s), np.arange(1, min(31, N - 1)), np.arange(max(1, N - 31), N - 1)]))
            n1[(x, y)] = (nas, core.n1_profile(Q, mu, x, y, k, N, T, nas))
    best = None
    nneg = 0
    ncell = 0
    for (i, j) in itertools.permutations(range(3), 2):
        if Q[i, j] * Q[j, i] == 0:
            continue
        k = 3 - i - j
        for d in deltas:
            v = {i: d, j: 0.0, k: -M}
            lead = core.leading_scores(S, [v[0], v[1], v[2]], tau)
            order = sorted(lead.items(), key=lambda kv: kv[1])
            if len(order[0][0]) == 3 or order[1][1] - order[0][1] < 0.5:
                continue
            ex = {(s_,): core.log_single(Q, mu, s_, N, T, v[s_]) for s_ in range(3)}
            for (x, y), pr in profs.items():
                if pr is None:
                    continue
                nas, lp = pr
                ex[(x, y)] = float((lp + T * (v[x] * nas + v[y] * (N - nas)) / N).max())
            best6 = max(ex.values())
            x, y = min(i, j), max(i, j)
            nas1, lp1 = n1[(x, y)]
            tot = lp1 + T * (v[x] * nas1 + v[y] * (N - 1 - nas1) + v[k]) / N
            m = best6 - float(tot.max())
            ncell += 1
            nneg += m < 0
            if best is None or m < best[0]:
                best = (m, (i + 1, j + 1), float(d), tuple(s_ + 1 for s_ in order[0][0]))
    return dict(name=name, N=N, ti=ti, tau=float(tau), status="ok", min_margin=None if best is None else best[0],
                at=None if best is None else best[1:], ncell=ncell, nneg=int(nneg))


if __name__ == "__main__":
    name = sys.argv[1]
    Ns = [int(x) for x in sys.argv[2:]]
    TIS = [int(x) for x in os.environ.get('N1_TI', '0,1,2,3,4,5,6,7,8').split(',')]
    jobs = [(name, N, ti) for N in Ns for ti in TIS]
    with Pool(9) as p:
        res = p.map(job, jobs)
    tag = os.environ.get('N1_TAG', '')
    json.dump(res, open(os.path.join(HERE, f"03_task2_n1_{name}{tag}.json"), "w"), default=float)
    Q, pi, mu, S, R, b, q = sc.build(name)
    H, tau0, U, M = core.design_constants(R, b)
    print(f"\n### {name}: R={R:.3f} b={b:.4f} U={U:.1f} M={M:.0f}; min over cells (gap>=0.5) of log(best six faces) - log(best n_k=1 composition); '-' inadmissible, 's' skipped (cost)")
    print("| tau | " + " | ".join(f"N={N}" for N in Ns) + " |")
    print("|---:|" + "---:|" * len(Ns))
    taus, _ = sc.grids(R, U)
    for ti in TIS:
        row = []
        for N in Ns:
            r = next(x for x in res if x["N"] == N and x["ti"] == ti)
            if r["status"] == "inadmissible":
                row.append("-")
            elif r["status"] == "skipped":
                row.append("s")
            elif r["min_margin"] is None:
                row.append("no cells")
            else:
                row.append(f"{r['min_margin']:.2f}" + (f" ({r['nneg']} neg)" if r["nneg"] else ""))
        print(f"| {taus[ti]:.3f} | " + " | ".join(row) + " |")
