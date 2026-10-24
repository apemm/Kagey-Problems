"""Check the coarse-then-refine maximizer and the run-count truncation K against the full
computation, at N = 5000 and 20000, for the T5-C generator (pair 2->1 in 1-based labels)."""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from importlib import import_module
core = import_module("03_core")
pi = np.array([0.25, 0.35, 0.40])
c = np.array([[0, .45, .34], [.45, 0, .37], [.34, .37, 0]])
Q = core.reversible_generator(pi, c)
S, R, b, q, w = core.class_data(Q, pi)
H = 2 * R
mu = np.array([0.3, 0.3, 0.4])
for N in (5000, 20000):
    for (i, j) in [(1, 0), (2, 1)]:
        t = core.limit_t_ij(Q, i, j, H)
        tau = 0.85 * t
        T = tau * np.log(N)
        t0 = time.time()
        nas, lp = core.log_pair_array(Q, mu, i, j, N, T, stride=(1 if N <= 5000 else 3))
        tot = lp + T * (H * nas) / N
        full = tot.max()
        t1 = time.time()
        fast, nstar = core.best_pair_fast(Q, mu, i, j, N, T, H, 0.0, full_below=1000)
        t2 = time.time()
        K0 = core.runs_K(Q, i, j, N, T)
        nas2, lp2 = core.log_pair_array(Q, mu, i, j, N, T, nas=[nstar], K=K0)
        nas3, lp3 = core.log_pair_array(Q, mu, i, j, N, T, nas=[nstar], K=2 * K0)
        print(f"N={N} pair=({i+1},{j+1}) tau={tau:.4f} T={T:.2f} full(stride)={full:.10f} fast={fast:.10f} "
              f"diff={fast-full:.2e} argmax n_a={nstar} K={K0} Kdouble_diff={lp3[0]-lp2[0]:.2e} "
              f"time full {t1-t0:.1f}s fast {t2-t1:.1f}s")
