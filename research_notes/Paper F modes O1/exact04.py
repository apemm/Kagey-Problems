# exact04.py -- exact law of the plus count A_N, written independently of
# engine.py, for the fourth round (upper bound for the number of modes).
# Paper F (problem 131), modal structure (O1).
#
# Rows are indexed by the minus count j, columns by the plus count k.
#   S[j,k] = P(a plus run starts after k plus and j minus steps)
#   E[j,k] = P(a minus run starts after k plus and j minus steps)
#   S[j,:] = S0[j,:] + sum_{l=1}^{j} f_-(l) E[j-l,:]
#   E[j,:] = E0[j,:] + (S[j,:] convolved with f_+ in k)
# Fresh plus start: S0[0,0] = 1; fresh minus: E0[0,0] = 1; fair: 1/2 each.
# The run in progress at step N gives
#   P_N(k) = sum_{x<k} S[N-k,x] T_+(k-x) + sum_{y<N-k} E[y,k] T_-(N-k-y).
# All sums have nonnegative terms (direct convolutions, no FFT), float64.
# Run checks with: py -I exact04.py
import numpy as np
from scipy.special import zeta as hz


def zeta_law(alpha, nmax, nmin=1):
    """f(n) = n^(-alpha-1)/zeta(alpha+1, nmin) on n >= nmin; T(m) = P(X >= m).
    Arrays of length nmax+2 (index = n)."""
    s = alpha + 1.0
    z = hz(s, nmin)
    f = np.zeros(nmax + 2)
    n = np.arange(nmin, nmax + 2, dtype=float)
    f[nmin:] = n ** (-s) / z
    T = np.ones(nmax + 2)
    T[nmin:] = hz(s, n) / z
    return f, T


def mean_of(alpha, nmin=1):
    return hz(alpha, nmin) / hz(alpha + 1.0, nmin) if nmin == 1 else \
        (hz(alpha, nmin)) / hz(alpha + 1.0, nmin)


def rows(fp, fm, N, J, wplus=1.0, wminus=0.0):
    """S, E for rows j = 0..J and columns k = 0..N (k + j <= N used)."""
    K = N + 1
    S = np.zeros((J + 1, K)); E = np.zeros((J + 1, K))
    fpv = fp[:K].copy(); fpv[0] = 0.0
    fmv = fm[:J + 1].copy(); fmv[0] = 0.0
    for j in range(J + 1):
        Kj = N - j + 1
        r = np.zeros(Kj)
        if j == 0:
            r[0] = wplus
        else:
            r += fmv[j:0:-1] @ E[:j, :Kj]   # sum_{i<j} f_-(j-i) E[i,:]
        S[j, :Kj] = r
        E[j, :Kj] = np.convolve(r, fpv[:Kj])[:Kj]
        if j == 0:
            E[0, 0] += wminus
    return S, E


def P_at(S, E, Tp, Tm, N, k):
    j = N - k
    v = 0.0
    if k >= 1:
        v += S[j, :k] @ Tp[k:0:-1]
    if j >= 1:
        v += E[:j, k] @ Tm[j:0:-1]
    return v


def law_full(fp, Tp, fm, Tm, N, wplus=1.0, wminus=0.0):
    S, E = rows(fp, fm, N, N, wplus, wminus)
    return np.array([P_at(S, E, Tp, Tm, N, k) for k in range(N + 1)])


def law_layer(fp, Tp, fm, Tm, N, J, wplus=1.0, wminus=0.0):
    """g[j] = P_N(N-j) for j = 0..J."""
    S, E = rows(fp, fm, N, J, wplus, wminus)
    return np.array([P_at(S, E, Tp, Tm, N, N - j) for j in range(J + 1)])


def renewal(f, jmax):
    u = np.zeros(jmax + 1); u[0] = 1.0
    for j in range(1, jmax + 1):
        u[j] = f[1:j + 1] @ u[j - 1::-1]
    return u


def modes(P):
    """Local maxima with the paper's convention (plateaus once, endpoints
    count when they beat their neighbour). Returns list of block starts."""
    n = len(P)
    out = []
    i = 0
    while i < n:
        b = i
        while b + 1 < n and P[b + 1] == P[i]:
            b += 1
        left = (i == 0) or P[i - 1] < P[i]
        right = (b == n - 1) or P[b + 1] < P[i]
        if left and right:
            out.append(i)
        i = b + 1
    return out


def minima(P):
    return modes(-np.asarray(P))


def brute(fp, fm, N, wplus, wminus):
    """Markov chain over (plus count, sign, age of current run)."""
    from collections import defaultdict
    hp = lambda f, a: f[a] / max(1e-300, 1.0 - f[1:a].sum())  # P(X=a | X>=a)
    st = defaultdict(float)
    st[(1, '+', 1)] += wplus
    st[(0, '-', 1)] += wminus
    for _ in range(N - 1):
        nx = defaultdict(float)
        for (k, sg, a), p in st.items():
            f = fp if sg == '+' else fm
            h = hp(f, a)
            if sg == '+':
                nx[(k + 1, '+', a + 1)] += p * (1 - h)
                nx[(k, '-', 1)] += p * h
            else:
                nx[(k, '-', a + 1)] += p * (1 - h)
                nx[(k + 1, '+', 1)] += p * h
        st = nx
    P = np.zeros(N + 1)
    for (k, sg, a), p in st.items():
        P[k] += p
    return P


if __name__ == "__main__":
    for nmin in (1, 2):
        fp, Tp = zeta_law(1.5, 40, nmin)
        fm, Tm = zeta_law(1.2, 40, nmin)
        for N in (3, 7, 15):
            for w in ((1, 0), (0, 1), (0.5, 0.5)):
                a = law_full(fp, Tp, fm, Tm, N, *w)
                b = brute(fp, fm, N, *w)
                print("nmin", nmin, "N", N, "start", w,
                      "max|exact-brute| = %.1e" % abs(a - b).max(),
                      "sum = %.15f" % a.sum())
