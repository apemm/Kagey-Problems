"""The two-state run polynomial and recurrence used by Papers C and E.

These helpers were extracted unchanged from paperC/verify_sticky_fisher.py.
They use numpy and scipy, and do not import a paper-specific verification script.
"""
from math import log

import numpy as np
from scipy.optimize import brentq
from scipy.special import gammaln


def logS(a, b, u):
    """log S_{a,b}(u) in log space (float)."""
    m1 = np.arange(1, a + 1)
    lu = log(u)
    lC = lambda n, r: gammaln(n + 1) - gammaln(r + 1) - gammaln(n - r + 1)
    terms = []
    for dm, c in ((-1, 1.0), (0, 2.0), (1, 1.0)):
        m2 = m1 + dm
        ok = (m2 >= 1) & (m2 <= b)
        t = log(c) + lC(a - 1, m1[ok] - 1) + lC(b - 1, m2[ok] - 1) + (m1[ok] + m2[ok] - 1) * lu
        terms.append(t)
    t = np.concatenate(terms)
    mx = t.max()
    return mx + log(np.exp(t - mx).sum())


def uN_runs(N):
    """Paper A's root: S_{N/2,N/2}(u) = 1 (method A, run formula)."""
    return brentq(lambda u: logS(N // 2, N - N // 2, u), 1e-9, 1.0, xtol=1e-16, rtol=1e-15)


def paperA_law(N, q):
    """P(K = k), k = 0..N, by Paper A's recurrence (works for complex q)."""
    p = 1 - q
    R = np.zeros(N + 1, dtype=complex)
    Lf = np.zeros(N + 1, dtype=complex)
    R[1] = 0.5
    Lf[0] = 0.5
    for n in range(2, N + 1):
        R2 = np.zeros(N + 1, dtype=complex)
        R2[1:] = p * R[:-1] + q * Lf[:-1]
        L2 = p * Lf + q * R
        R, Lf = R2, L2
    return R + Lf


def uN_dp(N):
    """Paper A's root from the recurrence: P_N(N/2) = P_N(0) (method B)."""
    f = lambda q: (lambda P: log(P[N // 2].real) - log(P[0].real))(paperA_law(N, q))
    q = brentq(f, 1e-6, min(0.5, 20 * log(N) / N), xtol=1e-15, rtol=1e-14)
    return q / (1 - q)
