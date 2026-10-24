"""Validation of the exact pair formula, the capped DP and the singleton formula
against the full three-state dynamic program (N = 60, 120)."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from importlib import import_module
core = import_module("03_core")

pi = np.array([0.25, 0.35, 0.40])
c = np.array([[0, 0.12, 0.09], [0.12, 0, 0.10], [0.09, 0.10, 0]])
Q = core.reversible_generator(pi, c)
mu = np.array([0.3, 0.3, 0.4])
for N, T in [(60, 5.0), (120, 9.0)]:
    full = core.full3_logprobs(Q, mu, N, T)  # [n0,n1], n2 = N-n0-n1
    print(f"N={N} T={T}")
    # pair {0,1}: n2=0
    err = 0.0
    nas, lp = core.log_pair_array(Q, mu, 0, 1, N, T)
    for na, l in zip(nas, lp):
        err = max(err, abs(l - full[na, N - na]))
    print("  pair(0,1) max abs log error vs DP:", err)
    nas, lp = core.log_pair_array(Q, mu, 0, 2, N, T)
    err = max(abs(l - full[na, 0]) for na, l in zip(nas, lp))
    print("  pair(0,2) max abs log error vs DP:", err)
    nas, lp = core.log_pair_array(Q, mu, 1, 2, N, T)
    err = max(abs(l - full[0, na]) for na, l in zip(nas, lp))
    print("  pair(1,2) max abs log error vs DP:", err)
    for s in range(3):
        v = [0, 0, 0]
        ex = core.log_single(Q, mu, s, N, T, 0.0)
        dpv = full[N, 0] if s == 0 else (full[0, N] if s == 1 else full[0, 0])
        print(f"  singleton {s}: formula {ex:.12f} dp {dpv:.12f}")
    # capped vs full (i=0, k=2)
    cap = core.capped_logprobs(Q, mu, N, T, 0, 2, 4)
    err = 0.0
    for n0 in range(0, N + 1):
        for nk in range(0, 5):
            n1 = N - n0 - nk
            if n1 < 0:
                continue
            a = cap[n0, nk]
            b = full[n0, n1]
            if np.isfinite(a) and np.isfinite(b):
                err = max(err, abs(a - b))
            elif np.isfinite(a) != np.isfinite(b) and max(a, b) > -600:
                err = max(err, 99)
    print("  capped(i=0,k=2,L=4) max abs log error vs DP:", err)
    print("  total probability (logsumexp over all compositions):",
          float(np.log(np.exp(full[np.isfinite(full)]).sum())) if N <= 60 else "n/a")
