"""Exact law of the occupation count A_N for alternating runs, two methods and a brute force.

Used by 03_alpha_one_checks.py. Run this file alone to cross-check the methods:
    py -I 03_alpha_one_engine.py

Setting. Runs alternate in sign, all runs independent, plus runs with mass function f_+ and tail
T_+(n) = P(X_+ >= n), minus runs likewise. A fresh plus start begins with a full plus run.
P_N(k) = P(A_N = k), A_N = number of plus steps among the first N.

Method 1 (transform). With F(z) = sum f(n) z^n and Tc(z) = sum_{n>=1} T(n) z^n, the fresh plus
start has double generating function
    G+(x, y) = sum_{k,j} P_{k+j}(k) x^k y^j = [Tc_+(x) + F_+(x) Tc_-(y)] / [1 - F_+(x) F_-(y)],
and the fresh minus start G-(x, y) = [Tc_-(y) + F_-(y) Tc_+(x)] / [1 - F_+(x) F_-(y)].
(Split on the run in progress at step N: A(k,j) = sum_m u+_m(k) u-_m(j) has generating function
1/(1 - F_+ F_-).) Put x = t w, y = t. The coefficient of t^N is a polynomial of degree <= N in w.
t runs over the circle of radius r with M points, w over the M-th roots of unity, M >= 4(N+1),
r^M = 1e-14, so the aliasing error is below 1e-14 r^-N, about 1e-10 at worst.

Method 2 (direct run recursion, O(N^3)). S(k,j), E(k,j) = probability that a plus (minus) run
starts after exactly k plus and j minus steps; S = delta + E *_j f_-, E = S *_k f_+, and
P_N(k) = sum_{x<k} S(x, N-k) T_+(k-x) + sum_{y<N-k} E(k, y) T_-(N-k-y).

Method 3 (brute force). Sum over all sign strings of length N <= 12.
"""
import itertools
import math

import numpy as np


# ---------------------------------------------------------------- laws, given by their tails

class Law:
    """A run law on {1, 2, ...} given by T(n) = P(X >= n) with T(1) = 1, and its mass function."""

    def __init__(self, name, T, f=None, index=1.0):
        self.name = name
        self._T = T
        self._f = f
        self.index = index

    def T(self, n):
        n = np.asarray(n, dtype=float)
        return np.where(n <= 1, 1.0, self._T(np.maximum(n, 1.0)))

    def f(self, n):
        n = np.asarray(n, dtype=float)
        if self._f is not None:
            return np.where(n >= 1, self._f(np.maximum(n, 1.0)), 0.0)
        return np.where(n >= 1, self.T(n) - self.T(n + 1), 0.0)

    def arrays(self, nmax):
        """f[0..nmax], T[0..nmax] with f[0] = 0, T[0] = 1."""
        n = np.arange(nmax + 1, dtype=float)
        return self.f(n), self.T(n)


def law_Q1():
    # T(n) = 1/n, f(n) = 1/(n(n+1)); L = 1, mu(x) = H_{x+1} - 1
    return Law("Q1: T=1/n", lambda n: 1.0 / n, lambda n: 1.0 / (n * (n + 1.0)))


def law_Q2():
    # T(n) = log 2 / (n log(n+1)); f ~ log 2/(n^2 log n); mu ~ log 2 log log x (barely infinite mean)
    c = math.log(2.0)
    T = lambda n: c / (n * np.log1p(n))
    def f(n):
        # T(n) - T(n+1) without cancellation
        a = n * np.log1p(n)
        b = (n + 1.0) * np.log1p(n + 1.0)
        return c * (b - a) / (a * b)
    return Law("Q2: T=log2/(n log(n+1))", T, f)


def law_Q3():
    # T(n) = 2/(n+1), f(n) = 2/((n+1)(n+2)); L -> 2
    return Law("Q3: T=2/(n+1)", lambda n: 2.0 / (n + 1.0), lambda n: 2.0 / ((n + 1.0) * (n + 2.0)))


def law_power(beta):
    # T(n) = n^(-beta), index beta
    T = lambda n: n ** (-beta)
    f = lambda n: -(n ** (-beta)) * np.expm1(-beta * np.log1p(1.0 / n))
    return Law("T=n^-%g" % beta, T, f, index=beta)


# ---------------------------------------------------------------- method 1: transform

def _series_on_circle(coef_fn, r, M, nterms):
    """values sum_{n>=1} c(n) r^n e^{2 pi i n l / M}, l = 0..M-1, coefficients folded mod M."""
    n = np.arange(nterms, dtype=float)
    c = coef_fn(n) * r ** n
    c[0] = 0.0
    g = np.zeros(M)
    for start in range(0, nterms, M):
        seg = c[start:start + M]
        g[: len(seg)] += seg
    return M * np.fft.ifft(g)


def exact_law(lp, lm, N, chunk=96, eps=1e-14):
    """(fresh plus law, fresh minus law), arrays over k = 0..N."""
    M = 1 << int(math.ceil(math.log2(4 * (N + 1))))
    r = math.exp(math.log(eps) / M)
    nterms = 3 * M
    Fp = _series_on_circle(lp.f, r, M, nterms)
    Tp = _series_on_circle(lp.T, r, M, nterms)
    Fm = _series_on_circle(lm.f, r, M, nterms)
    Tm = _series_on_circle(lm.T, r, M, nterms)
    Fp2 = np.concatenate([Fp, Fp])
    Tp2 = np.concatenate([Tp, Tp])
    from numpy.lib.stride_tricks import sliding_window_view
    FpW = sliding_window_view(Fp2, M)  # row s: Fp[(l + s) mod M]
    TpW = sliding_window_view(Tp2, M)
    l = np.arange(M)
    wt = np.exp(-2j * np.pi * ((l * N) % M) / M) * (r ** (-N) / M)
    cp = np.empty(M, dtype=complex)
    cm = np.empty(M, dtype=complex)
    for s0 in range(0, M, chunk):
        s1 = min(M, s0 + chunk)
        fx = FpW[s0:s1]
        tx = TpW[s0:s1]
        den = 1.0 - fx * Fm[None, :]
        Gp = (tx + fx * Tm[None, :]) / den
        Gm = (Tm[None, :] + Fm[None, :] * tx) / den
        cp[s0:s1] = Gp @ wt
        cm[s0:s1] = Gm @ wt
    # c(w_s) = sum_k P(k) w_s^k with w_s = e^{2 pi i s/M}; invert
    Pp = np.fft.fft(cp)[: N + 1].real / M
    Pm = np.fft.fft(cm)[: N + 1].real / M
    return Pp, Pm


# ---------------------------------------------------------------- method 2: direct recursion

def direct_law(lp, lm, N):
    fp, Tp = lp.arrays(N + 1)
    fm, Tm = lm.arrays(N + 1)
    S = np.zeros((N + 1, N + 1))
    E = np.zeros((N + 1, N + 1))
    S2 = np.zeros((N + 1, N + 1))  # fresh minus start
    E2 = np.zeros((N + 1, N + 1))
    S[0, 0] = 1.0
    E2[0, 0] = 1.0
    for n in range(1, N + 1):
        for k in range(0, n + 1):
            j = n - k
            if j >= 1:
                ys = np.arange(1, j + 1)
                S[k, j] = np.dot(fm[ys], E[k, j - ys])
                S2[k, j] = np.dot(fm[ys], E2[k, j - ys])
            if k >= 1:
                xs = np.arange(1, k + 1)
                E[k, j] = np.dot(fp[xs], S[k - xs, j])
                E2[k, j] = np.dot(fp[xs], S2[k - xs, j])
    Pp = np.zeros(N + 1)
    Pm = np.zeros(N + 1)
    for k in range(N + 1):
        j = N - k
        xs = np.arange(0, k)
        ys = np.arange(0, j)
        Pp[k] = np.dot(S[xs, j], Tp[k - xs]) + np.dot(E[k, ys], Tm[j - ys])
        Pm[k] = np.dot(S2[xs, j], Tp[k - xs]) + np.dot(E2[k, ys], Tm[j - ys])
    return Pp, Pm


# ---------------------------------------------------------------- method 3: sign strings

def brute_law(lp, lm, N, first=+1):
    P = np.zeros(N + 1)
    for rest in itertools.product((1, -1), repeat=N - 1):
        s = (first,) + rest
        runs = []
        cur, ln = s[0], 1
        for x in s[1:]:
            if x == cur:
                ln += 1
            else:
                runs.append((cur, ln))
                cur, ln = x, 1
        runs.append((cur, ln))
        pr = 1.0
        for sg, ln in runs[:-1]:
            pr *= float((lp if sg > 0 else lm).f(ln))
        sg, ln = runs[-1]
        pr *= float((lp if sg > 0 else lm).T(ln))
        P[sum(1 for x in s if x > 0)] += pr
    return P


# ---------------------------------------------------------------- renewal quantities

def renewal(law, nmax):
    """u(j) = sum_m f^{*m}(j), and V(j) = sum_m m f^{*m}(j), j = 0..nmax."""
    f, _ = law.arrays(nmax)
    u = np.zeros(nmax + 1)
    u[0] = 1.0
    for n in range(1, nmax + 1):
        u[n] = np.dot(f[1:n + 1], u[n - 1::-1])
    # V = F/(1-F)^2 = u * (u - delta0): V(j) = sum_{i} u(i) (u - delta)(j - i)
    w = u.copy()
    w[0] = 0.0
    V = np.convolve(u, w)[: nmax + 1]
    return u, V


def truncated_mean(law, xmax):
    """mu(x) = sum_{n <= x} n f(n) for integer x = 0..xmax."""
    n = np.arange(xmax + 1, dtype=float)
    return np.cumsum(n * law.f(n))


if __name__ == "__main__":
    import time
    for (lp, lm) in [(law_Q1(), law_Q1()), (law_Q1(), law_Q3()), (law_Q2(), law_power(0.5)),
                     (law_Q1(), law_power(1.5))]:
        worst_b = 0.0
        for N in range(1, 13):
            Pp, Pm = exact_law(lp, lm, N)
            B = brute_law(lp, lm, N, +1)
            Bm = brute_law(lp, lm, N, -1)
            worst_b = max(worst_b, np.abs(Pp - B).max(), np.abs(Pm - Bm).max())
        t0 = time.time()
        Pp, Pm = exact_law(lp, lm, 300)
        Dp, Dm = direct_law(lp, lm, 300)
        print("%-28s %-12s brute N<=12: %.2e   direct N=300: %.2e   sums-1: %.1e %.1e"
              % (lp.name, lm.name, worst_b, max(np.abs(Pp - Dp).max(), np.abs(Pm - Dm).max()),
                 Pp.sum() - 1, Pm.sum() - 1))
