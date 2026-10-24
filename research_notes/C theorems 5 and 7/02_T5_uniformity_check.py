"""Finite-horizon pair-entry time for two-state chains across a compact class.

Exact controlled atoms Pr_mu(n) exp(T v.n/N) for the chain I + (T/N) Q on two
states, by the run expansion. For each chain in a class {q1 + q2 <= R, sqrt(q1 q2) >= b}
and the protected field v = (H, 0), H = 2R, we find the smallest tau at which the
pair {1,2} beats both singletons, and compare it with

    t_N^pred = t (1 - log L/(2L)) + c/L,    L = log N,
    t = 1/delta',  delta' = (q1 - H) - lambda_12(v),
    c = t (log(mu_1/K_12(v)) - log(t)/2),

which is what the crossing equation of the paper gives when the face maximum
formula holds for the controlled atom with constants uniform over the class.
The quantity L^2 (t_N - t_N^pred) should stay bounded, with a bound that does not
blow up across the class.

Run:  py -I 02_T5_uniformity_check.py
"""
import math
import numpy as np
from math import lgamma, log, sqrt, exp

def chain(q1, q2, pi1):
    """Two-state reversible chain with exit rates q1, q2 (so q12 = q1, q21 = q2)."""
    pi2 = 1.0 - pi1
    # detailed balance pi1 q12 = pi2 q21 forces pi1 q1 = pi2 q2, so pi1 is determined.
    pi1 = q2 / (q1 + q2)
    return q1, q2, pi1, 1 - pi1

def log_pair_atom(N, T, q1, q2, mu, v, a_vals, Mmax):
    """log of Pr(n) exp(T v.n/N) for n = (a, N-a), vectorised over a_vals."""
    h = T / N
    a = np.asarray(a_vals, dtype=np.int64)
    bcount = N - a
    out = np.full(a.shape, -np.inf)
    l1 = math.log1p(-h * q1)
    l2 = math.log1p(-h * q2)
    M = np.arange(2, Mmax + 1)
    for start in (1, 2):
        if start == 1:
            m1 = (M + 1) // 2
            m2 = M // 2
            logW = log(mu[0]) + m2 * log(q1) + (m1 - 1) * log(q2)
        else:
            m2 = (M + 1) // 2
            m1 = M // 2
            logW = log(mu[1]) + m1 * log(q2) + (m2 - 1) * log(q1)
        # binomials C(a-1, m1-1) C(b-1, m2-1), vectorised: shape (len(a), len(M))
        A = a[:, None] - 1
        B = bcount[:, None] - 1
        K1 = m1[None, :] - 1
        K2 = m2[None, :] - 1
        valid = (K1 <= A) & (K2 <= B)
        with np.errstate(invalid="ignore", divide="ignore"):
            lb = (lgamma_v(A + 1) - lgamma_v(K1 + 1) - lgamma_v(A - K1 + 1)
                  + lgamma_v(B + 1) - lgamma_v(K2 + 1) - lgamma_v(B - K2 + 1))
        terms = (logW[None, :] + (M[None, :] - 1) * log(h) + lb
                 + (A + 1 - m1[None, :]) * l1 + (B + 1 - m2[None, :]) * l2)
        terms = np.where(valid, terms, -np.inf)
        mx = terms.max(axis=1)
        s = np.log(np.exp(terms - mx[:, None]).sum(axis=1)) + mx
        out = np.logaddexp(out, s)
    out = out + h * (v[0] * a + v[1] * bcount)
    return out

from scipy.special import gammaln as _lg
def lgamma_v(x):
    return _lg(np.maximum(x, 1))

def pair_max(N, T, q1, q2, mu, v):
    """Maximum over a of the pair atom, by a four-stage zoom (400 points per stage,
    unimodality of the coarse profile is checked at the first stage)."""
    Mmax = int(min(N, 6 * T + 80))
    lo, hi = 1, N - 1
    for stage in range(4):
        grid = np.unique(np.clip(np.linspace(lo, hi, 400).astype(np.int64), 1, N - 1))
        vals = log_pair_atom(N, T, q1, q2, mu, v, grid, Mmax)
        j = int(np.argmax(vals))
        if stage == 0:
            d = np.diff(vals)
            assert np.all(d[:j] >= -1e-9) and np.all(d[j:] <= 1e-9), "coarse profile not unimodal"
        if hi - lo <= 400:
            return float(vals.max())
        lo = int(grid[max(j - 1, 0)])
        hi = int(grid[min(j + 1, len(grid) - 1)])
    grid = np.arange(lo, hi + 1, dtype=np.int64)
    vals = log_pair_atom(N, T, q1, q2, mu, v, grid, Mmax)
    return float(vals.max())

def log_singletons(N, T, q1, q2, mu, v):
    h = T / N
    s1 = log(mu[0]) + (N - 1) * math.log1p(-h * q1) + T * v[0]
    s2 = log(mu[1]) + (N - 1) * math.log1p(-h * q2) + T * v[1]
    return max(s1, s2)

def entry_time(N, q1, q2, mu, v, lo, hi):
    """Smallest tau in [lo, hi] with pair atom max > singleton max (bisection; the
    difference is checked to change sign once on a grid first)."""
    L = log(N)
    def gap(tau):
        T = tau * L
        return pair_max(N, T, q1, q2, mu, v) - log_singletons(N, T, q1, q2, mu, v)
    grid = np.linspace(lo, hi, 9)
    g = [gap(t) for t in grid]
    signs = [bool(x > 0) for x in g]
    changes = [i for i in range(1, len(signs)) if signs[i] != signs[i - 1]]
    assert signs[0] is False and signs[-1] is True, (signs[0], signs[-1])
    assert len(changes) == 1, f"sign changes at {changes}"
    a, b = grid[changes[0] - 1], grid[changes[0]]
    for _ in range(24):
        m = 0.5 * (a + b)
        if gap(m) > 0:
            b = m
        else:
            a = m
    return 0.5 * (a + b)

def prediction(q1, q2, pi, mu, v, N):
    """t, c and the predicted entry time from the crossing equation."""
    w = q1 * q2
    sw = sqrt(w)
    S = np.array([[q1, -sw], [-sw, q2]])
    Sv = S - np.diag(v)
    evals, evecs = np.linalg.eigh(Sv)
    lam = evals[0]
    psi = evecs[:, 0]
    if psi[0] < 0:
        psi = -psi
    alpha = psi ** 2
    sp = np.sqrt(np.array(pi))
    r = psi / sp
    l = psi * sp
    c12 = psi[0] * psi[1] * sw
    K = (mu @ r) * (l.sum()) / sqrt(4 * math.pi) * sqrt(c12) / (alpha[0] * alpha[1])
    dprime = (q1 - v[0]) - lam
    t = 1.0 / dprime
    c = t * (log(mu[0] / K) - 0.5 * log(t))
    L = log(N)
    return t, c, K, t * (1 - log(L) / (2 * L)) + c / L

if __name__ == "__main__":
    R, b = 3.0, 1.0
    H = 2 * R
    v = (H, 0.0)
    chains = [(1.0, 1.0), (0.5, 2.0), (2.0, 0.5), (1.5, 1.5), (0.4, 2.5), (2.5, 0.4)]
    Ns = [10**4, 10**5, 10**6, 10**7]
    print(f"class R={R}, b={b}, field v={v}; start mu=(0.5,0.5)")
    print("chain (q1,q2)  N      t_N(exact)   t_N(pred)    L^2*(t_N-pred)   t     c      K")
    for q1, q2 in chains:
        assert q1 + q2 <= R and sqrt(q1 * q2) >= b
        pi = (q2 / (q1 + q2), q1 / (q1 + q2))
        mu = np.array([0.5, 0.5])
        for N in Ns:
            t, c, K, pred = prediction(q1, q2, pi, mu, v, N)
            L = log(N)
            tN = entry_time(N, q1, q2, mu, v, 0.5 * t, 1.5 * t)
            print(f"({q1:4.2f},{q2:4.2f})  {N:8d}  {tN:10.6f}  {pred:10.6f}  {L*L*(tN-pred):12.4f}  {t:6.3f} {c:7.3f} {K:7.4f}")
