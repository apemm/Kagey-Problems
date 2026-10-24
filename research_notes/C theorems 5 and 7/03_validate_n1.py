"""Validate the exact n_k = 1 insertion formula against the capped dynamic programme."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from importlib import import_module
core = import_module("03_core")
T1 = import_module("03_task1_compute")
Q, MU = T1.Q, T1.MU
for N, T in [(60, 5.0), (150, 12.0), (300, 20.0)]:
    for (a, b, k) in [(0, 1, 2), (1, 2, 0), (2, 0, 1)]:
        cap = core.capped_logprobs(Q, MU, N, T, a, k, 1)  # [n_a, n_k], n_b implicit
        nas = np.arange(1, N - 1)
        mine = core.n1_profile(Q, MU, a, b, k, N, T, nas, K=N // 2)
        ref = np.array([cap[na, 1] for na in nas])
        ok = np.isfinite(ref)
        print(f"N={N} T={T} (a,b,k)={(a,b,k)}  max |log diff| = {np.max(np.abs(mine[ok]-ref[ok])):.2e}  (n compositions {ok.sum()})")
