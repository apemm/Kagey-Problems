"""Exact law of the occupation count A_N by the run recursion, for two arbitrary run laws.

Run:  py -I 01_exact_law.py     (brute-force check of the recursion for N <= 11)

A[m, k] = P(a plus run starts after k plus and m minus steps), B[m, k] the same for a minus run.
Fresh plus start: A[0, 0] = 1; fresh minus start: B[0, 0] = 1. For k + m <= Nmax - 1,
    B[m, k] = sum_{l=1}^{k} f_+(l) A[m, k-l],     A[m, k] = sum_{l=1}^{m} f_-(l) B[m-l, k].
The run in progress at step N is censored, so for every N <= Nmax
    P_N(N-m) += sum_k A[m, k] T_+(N-k-m),         P_N(k) += sum_m B[m, k] T_-(N-k-m).
All terms are nonnegative (no cancellation); cost O(Nmax^3) once, then O(N^2) per N.
"""
import itertools

import numpy as np
from scipy.special import zeta


def zeta_law(a, nmax):
    """f(n) = n^(-a-1)/zeta(a+1) and T(n) = P(X >= n) for 0 <= n <= nmax + 1."""
    z = zeta(a + 1)
    n = np.arange(nmax + 2, dtype=float)
    f = np.zeros(nmax + 2)
    f[1:] = n[1:] ** (-a - 1) / z
    T = np.ones(nmax + 2)
    T[1:] = zeta(a + 1, n[1:]) / z
    return f, T


def run_arrays(fp, fm, Nmax, start='+'):
    A = np.zeros((Nmax, Nmax))
    B = np.zeros((Nmax, Nmax))
    if start == '+':
        A[0, 0] = 1.0
    else:
        B[0, 0] = 1.0
    for m in range(Nmax):
        L = Nmax - m
        if m >= 1:
            A[m, :L] += fm[m:0:-1] @ B[0:m, :L]
        B[m, :L] += np.convolve(A[m, :L], fp[:L])[:L]
    return A, B


def law(A, B, Tp, Tm, N):
    P = np.zeros(N + 1)
    for m in range(N):
        L = N - m
        P[N - m] += A[m, :L] @ Tp[L:0:-1]
        P[0:L] += B[m, :L] * Tm[L:0:-1]
    return P


def renewal(f, J):
    u = np.zeros(J + 1)
    u[0] = 1.0
    for n in range(1, J + 1):
        u[n] = f[1:n + 1] @ u[n - 1::-1]
    return u


def brute(fp, Tp, fm, Tm, N, start='+'):
    P = np.zeros(N + 1)
    for s in itertools.product('+-', repeat=N):
        if s[0] != start:
            continue
        runs = [(k, len(list(g))) for k, g in itertools.groupby(s)]
        pr = 1.0
        for i, (sg, ln) in enumerate(runs):
            last = i == len(runs) - 1
            if sg == '+':
                pr *= Tp[ln] if last else fp[ln]
            else:
                pr *= Tm[ln] if last else fm[ln]
        P[s.count('+')] += pr
    return P


if __name__ == '__main__':
    fp, Tp = zeta_law(0.6, 40)
    fm, Tm = zeta_law(1.5, 40)
    worst = 0.0
    for start in '+-':
        A, B = run_arrays(fp, fm, 12, start)
        for N in range(1, 12):
            P = law(A, B, Tp, Tm, N)
            Q = brute(fp, Tp, fm, Tm, N, start)
            worst = max(worst, np.max(np.abs(P - Q)), abs(P.sum() - 1))
    print(f'recursion vs brute force, N <= 11, both starts: max deviation {worst:.2e}')
