"""Check that faces containing the suppressed state k lose at the finite-N pair-entry points of Task 1.
For each (pair (i,j), N) at tau = tau_N (from 03_task1_results.json) compute exactly (dynamic programming)
the maximum of Pr(n) exp(T v.n/N) over all compositions with n_k <= L (L = N for N <= 200: the full law)
and compare with the pair/singleton winner value.  Compositions with n_k > L are bounded by
exp(T H - M T (L+1)/N)  (Pr <= 1, n_i <= N)."""
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
from importlib import import_module
core = import_module("03_core")
from multiprocessing import Pool
T1 = import_module("03_task1_compute")
Q, MU, H, M, q = T1.Q, T1.MU, T1.H, T1.M, T1.q
res = json.load(open(os.path.join(HERE, "03_task1_results.json")))
tau_tab = {(r["i"], r["j"], r["N"]): r["tauN"] for r in res["pair"] if r.get("tauN")}


def job(a):
    i, j, N = a
    k = 3 - i - j
    tau = tau_tab[(i, j, N)]
    T = tau * np.log(N)
    v = np.zeros(3)
    v[i], v[j], v[k] = H, 0.0, -M
    sing = max(core.log_single(Q, MU, i, N, T, H), core.log_single(Q, MU, j, N, T, 0.0))
    L = min(N, int(np.ceil(80 * N / (M * T))) + 1)
    if N <= 200:
        full = core.full3_logprobs(Q, MU, N, T)  # [n0,n1], n2 implicit
        best = -np.inf
        for n0 in range(N + 1):
            for n1 in range(N + 1 - n0):
                n = np.array([n0, n1, N - n0 - n1])
                if n[k] == 0 or not np.isfinite(full[n0, n1]):
                    continue
                best = max(best, full[n0, n1] + T * (v @ n) / N)
        bound_rest = -np.inf
        Ltxt = "all"
    else:
        cap = core.capped_logprobs(Q, MU, N, T, i, k, L)
        best = -np.inf
        for ni in range(N + 1):
            for nk in range(1, L + 1):
                nj = N - ni - nk
                if nj < 0 or not np.isfinite(cap[ni, nk]):
                    continue
                best = max(best, cap[ni, nk] + T * (H * ni - M * nk) / N)
        bound_rest = T * H - M * T * (L + 1) / N
        Ltxt = str(L)
    return i, j, N, tau, sing, best, bound_rest, Ltxt


if __name__ == "__main__":
    Ns = [int(x) for x in sys.argv[1:]] or [200, 500, 1000, 2000]
    jobs = [(i, j, N) for N in Ns for (i, j) in T1.PAIRS if (i, j, N) in tau_tab]
    with Pool(12) as p:
        out = p.map(job, jobs)
    print("pair(1-based) | N | tau_N | log winner (singleton at the crossing) | log best face containing k, n_k<=L | L | log bound for n_k>L | margin (winner - best k-face)")
    for i, j, N, tau, sing, best, br, Lt in sorted(out, key=lambda x: (x[2], x[0], x[1])):
        print(f"({i+1},{j+1}) | {N} | {tau:.4f} | {sing:.3f} | {best:.3f} | {Lt} | {br:.1f} | {sing-best:.3f}")
