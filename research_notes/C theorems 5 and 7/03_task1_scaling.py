"""Fixed-T check of the face-maximum scaling M_pair / M_singleton ~ (K/mu_i) N^{-1} T^{1/2} e^{-T(lam_pair - lam_i)}.
If the exponent 1/2 of T is right, X(T,N) = [M_pair/M_i] * N * T^{-1/2} * e^{T(lam_pair-lam_i)} tends to a constant
(K/mu_i)(1 + O(1/T)) as N -> infinity at fixed T, and as T -> infinity.  Field v_i = H, v_j = 0.
Usage: py -I 03_task1_scaling.py"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from importlib import import_module
core = import_module("03_core")
from multiprocessing import Pool
pi = np.array([0.25, 0.35, 0.40])
c = np.array([[0, .45, .34], [.45, 0, .37], [.34, .37, 0]])
Q = core.reversible_generator(pi, c)
S, R, b, q, w = core.class_data(Q, pi)
H = 2 * R
MU = np.array([0.3, 0.3, 0.4])


def job(a):
    (i, j), T, N = a
    lam_i = q[i] - H
    A = S[np.ix_([i, j], [i, j])] - np.diag([H, 0.0])
    lam_p = np.linalg.eigvalsh(A)[0]
    sing = core.log_single(Q, MU, i, N, T, H)
    pair, ns = core.best_pair_fast(Q, MU, i, j, N, T, H, 0.0)
    X = np.exp(pair - sing + np.log(N) - 0.5 * np.log(T) + T * (lam_p - lam_i))
    return (i, j), T, N, X, ns / N


if __name__ == "__main__":
    jobs = [((i, j), T, N) for (i, j) in [(1, 0), (2, 1)] for T in (5, 10, 20, 40, 80) for N in (10 ** 5, 10 ** 6, 10 ** 7)]
    with Pool(12) as p:
        res = p.map(job, jobs)
    print("pair(1-based) | T | N | X = M_pair/M_i * N * T^-1/2 * exp(T(lam_pair-lam_i)) | argmax n_a/N")
    for (i, j), T, N, X, fr in res:
        print(f"({i+1},{j+1}) | {T} | {N:.0e} | {X:.5f} | {fr:.5f}")
    print("\nRatios X(2T)/X(T) at N=1e7 (T^{1/2}-law predicts 1 up to O(1/T); a T^{1}-law would give about 2)")
    d = {(p, T, N): X for (p, T, N, X, _) in res}
    for p in [(1, 0), (2, 1)]:
        print(p, [round(d[(p, 2 * T, 10 ** 7)] / d[(p, T, 10 ** 7)], 4) for T in (5, 10, 20, 40)])
