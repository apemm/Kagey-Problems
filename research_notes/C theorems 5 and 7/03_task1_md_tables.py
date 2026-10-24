"""Condensed markdown tables for 03_T5_numerics.md from 03_task1_results.json."""
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
from importlib import import_module
T1 = import_module("03_task1_compute")
core = import_module("03_core")
H = T1.H
res = json.load(open(os.path.join(HERE, "03_task1_results.json")))
pairs = {}
for r in res["pair"]:
    if r.get("tauN") is not None:
        pairs.setdefault((r["i"], r["j"]), {})[r["N"]] = r["tauN"]
Nsel = [200, 500, 1000, 2000, 5000, 20000, 100000, 1000000]
for (i, j) in sorted(pairs):
    t = core.limit_t_ij(T1.Q, i, j, H)
    print(f"\nOrdered pair (i,j) = ({i+1},{j+1}), limiting t_ij = {t:.5f}\n")
    print("| N | t_ij,N | t_ij | prediction | (t_ij,N - prediction) log N | kappa_N |")
    print("|---:|---:|---:|---:|---:|---:|")
    for N in Nsel:
        if N not in pairs[(i, j)]:
            continue
        tn = pairs[(i, j)][N]; L = np.log(N)
        pred = t * (1 - np.log(L) / (2 * L)); TN = tn * L
        print(f"| {N} | {tn:.5f} | {t:.5f} | {pred:.5f} | {(tn-pred)*L:.3f} | {L - TN/t - 0.5*np.log(TN):.4f} |")
