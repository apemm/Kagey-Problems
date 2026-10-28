"""Exact law of the occupation count A_N for the alternating renewal walk.

Run with `py -I`.  Notation as in papers F and G.  A run of sign s has mass function
f_s(n), n >= 1, and tail T_s(n) = P(X_s >= n).

For a fresh plus start let A(k, j) (B(k, j)) be the probability that a plus (minus) run
starts right after exactly k plus steps and j minus steps.  Then
    A(k, j) = delta_{k0} delta_{j0} + sum_{j' < j} B(k, j') f_-(j - j'),
    B(k, j) = sum_{k' < k} A(k', j) f_+(k - k'),
and, with j = N - k (the run-sum identity, G eq. (run-sum)),
    F^+_N(k) = sum_{k' < k} A(k', j) T_+(k - k') + sum_{j' < j} B(k, j') T_-(j - j').
For a fresh minus start the minus-run starts have the same A, the plus-run starts are
B'(k, j) = sum_{j' < j} A(k, j') f_-(j - j'), and
    F^-_N(k) = sum_{j' < j} A(k, j') T_-(j - j') + sum_{k' < k} B'(k', j) T_+(k - k').
A general initial run (nu_+, nu_-) uses the first-run decomposition (G Prop. first-run).

All sums have nonnegative terms and use direct convolution (no FFT), so the relative
rounding error of every probability is a small multiple of 1e-16 times the number of terms.
"""
import math
import numpy as np


# ----------------------------------------------------------------------------- laws

class Law:
    """A run law given by arrays f[0..n] (f[0] = 0) and T[0..n] (T[n] = P(X >= n))."""

    def __init__(self, name, f, T):
        self.name = name
        self.f = np.asarray(f, dtype=float)
        self.T = np.asarray(T, dtype=float)

    def renewal(self, n):
        """u(0..n), the renewal mass function, by the renewal equation."""
        f = self.f
        u = np.zeros(n + 1)
        u[0] = 1.0
        for j in range(1, n + 1):
            u[j] = np.dot(f[1:j + 1], u[j - 1::-1])
        return u


def sibuya(alpha, n):
    """Sibuya law: T(m) = prod_{i<m} (1 - alpha/i); generating function 1 - (1-z)^alpha.

    Completely monotone (a Beta mixture of geometric laws), f(m) ~ alpha m^{-1-alpha}/G(1-alpha),
    u(m) = Gamma(m+alpha)/(Gamma(alpha) m!) exactly."""
    T = np.zeros(n + 2)
    T[0] = 1.0
    T[1] = 1.0
    for m in range(1, n + 1):
        T[m + 1] = T[m] * (1.0 - alpha / m)
    f = np.zeros(n + 1)
    f[1:] = T[1:n + 1] - T[2:n + 2]
    return Law("sibuya(%g)" % alpha, f, T[:n + 1])


def zeta_law(alpha, n, start=1):
    """f(m) = m^{-1-alpha}/Z for m >= start."""
    from scipy.special import zeta
    Z = zeta(1.0 + alpha, start)
    m = np.arange(n + 1, dtype=float)
    f = np.zeros(n + 1)
    f[start:] = m[start:] ** (-1.0 - alpha) / Z
    T = np.ones(n + 1)
    for k in range(start + 1, n + 1):
        T[k] = zeta(1.0 + alpha, k) / Z
    return Law("zeta(%g,start=%d)" % (alpha, start), f, T)


def geom_mix(weights, thetas, n):
    """f(m) = sum_c w_c (1 - th_c) th_c^{m-1}; completely monotone."""
    m = np.arange(n + 1, dtype=float)
    f = np.zeros(n + 1)
    T = np.zeros(n + 1)
    for w, th in zip(weights, thetas):
        f[1:] += w * (1 - th) * th ** (m[1:] - 1)
        T[1:] += w * th ** (m[1:] - 1)
    T[0] = 1.0
    return Law("geom%s%s" % (tuple(weights), tuple(thetas)), f, T)


def mix(laws, weights, name=None):
    f = sum(w * L.f for L, w in zip(laws, weights))
    T = sum(w * L.T for L, w in zip(laws, weights))
    return Law(name or "mix", f, T)


# ----------------------------------------------------------------------------- engine

class Engine:
    """Holds FP[n, k] = F^+_n(k) and FM[n, k] = F^-_n(k) for 0 <= k <= n <= Nmax."""

    def __init__(self, lp, lm, Nmax):
        self.lp, self.lm, self.Nmax = lp, lm, Nmax
        N1 = Nmax + 1
        fp, fm = lp.f[:N1], lm.f[:N1]
        Tp, Tm = lp.T[:N1].copy(), lm.T[:N1].copy()
        Tp[0] = 0.0
        Tm[0] = 0.0
        # Store A and B transposed: At[j, k] = A(k, j).
        At = np.zeros((N1, N1))
        Bt = np.zeros((N1, N1))
        At[0, 0] = 1.0
        Bt[0, :] = np.convolve(At[0, :], fp)[:N1]
        for j in range(1, N1):
            km = N1 - j  # k = 0..Nmax-j
            At[j, :km] = fm[j:0:-1] @ Bt[:j, :km]
            Bt[j, :km] = np.convolve(At[j, :km], fp[:km])[:km]
        FP = np.zeros((N1, N1))
        FM = np.zeros((N1, N1))
        # C1(k, j) = sum_{k'<k} A(k', j) T_+(k-k')  (convolution in k for each j)
        C1t = np.zeros((N1, N1))
        for j in range(N1):
            km = N1 - j
            C1t[j, :km] = np.convolve(At[j, :km], Tp[:km])[:km]
        # C2(k, j) = sum_{j'<j} B(k, j') T_-(j-j')  (convolution in j for each k)
        A = np.ascontiguousarray(At.T)
        B = np.ascontiguousarray(Bt.T)
        del Bt
        C2 = np.zeros((N1, N1))
        for k in range(N1):
            jm = N1 - k
            C2[k, :jm] = np.convolve(B[k, :jm], Tm[:jm])[:jm]
        del B
        for n in range(N1):
            k = np.arange(n + 1)
            FP[n, :n + 1] = C1t[n - k, k] + C2[k, n - k]
        del C2
        # fresh minus: D1(k, j) = sum_{j'<j} A(k, j') T_-(j-j'); B'(k, j) = (A *_j f_-)(k, j);
        # D2(k, j) = sum_{k'<k} B'(k', j) T_+(k-k').
        D1 = np.zeros((N1, N1))
        Bp = np.zeros((N1, N1))
        for k in range(N1):
            jm = N1 - k
            D1[k, :jm] = np.convolve(A[k, :jm], Tm[:jm])[:jm]
            Bp[k, :jm] = np.convolve(A[k, :jm], fm[:jm])[:jm]
        Bpt = np.ascontiguousarray(Bp.T)
        del Bp, A
        D2t = C1t  # reuse memory
        D2t[:] = 0.0
        for j in range(N1):
            km = N1 - j
            D2t[j, :km] = np.convolve(Bpt[j, :km], Tp[:km])[:km]
        for n in range(N1):
            k = np.arange(n + 1)
            FM[n, :n + 1] = D1[k, n - k] + D2t[n - k, k]
        self.FP, self.FM = FP, FM
        self.At = At

    def fresh(self, N, sign=+1):
        return (self.FP if sign > 0 else self.FM)[N, :N + 1].copy()

    def fair(self, N, wplus=0.5):
        return wplus * self.FP[N, :N + 1] + (1 - wplus) * self.FM[N, :N + 1]

    def general(self, N, nu_p, nu_m):
        """nu_p[d], nu_m[d] for d = 1..; masses beyond the arrays are lumped as D >= N
        only if supplied; here Q_s(N) = sum_{d >= N} nu_s(d) must be given as nu arrays of
        length > N, with the tail sum taken from the array (caller supplies enough terms
        or the tail mass in the last entry via `tails`)."""
        P = np.zeros(N + 1)
        Qp = nu_p[N:].sum() if len(nu_p) > N else 0.0
        Qm = nu_m[N:].sum() if len(nu_m) > N else 0.0
        P[N] += Qp
        P[0] += Qm
        for d in range(1, min(N, len(nu_p))):
            if nu_p[d] != 0.0:
                n = N - d
                P[d:] += nu_p[d] * self.FM[n, :n + 1]
        for d in range(1, min(N, len(nu_m))):
            if nu_m[d] != 0.0:
                n = N - d
                P[:n + 1] += nu_m[d] * self.FP[n, :n + 1]
        return P


# ----------------------------------------------------------------------------- shape tools

def modes(P, rtol=0.0):
    """Local maxima of P (plateaus once, endpoints beat one neighbour).

    Differences with |dP| <= rtol * max(P[i], P[i+1]) are treated as ties.
    Returns (list of (a, b) blocks, list of local-minimum blocks, smallest relative gap)."""
    n = len(P)
    d = np.diff(P)
    scale = np.maximum(P[:-1], P[1:])
    rel = np.abs(d) / np.where(scale > 0, scale, 1.0)
    s = np.sign(d)
    s[rel <= rtol] = 0
    # blocks of equal values
    blocks = []
    a = 0
    for i in range(n - 1):
        if s[i] != 0:
            blocks.append((a, i))
            a = i + 1
    blocks.append((a, n - 1))
    maxima, minima = [], []
    for idx, (a, b) in enumerate(blocks):
        left = s[a - 1] if a > 0 else None   # sign of P[a]-P[a-1]
        right = s[b] if b < n - 1 else None  # sign of P[b+1]-P[b]
        up_left = (left is None) or left > 0
        down_right = (right is None) or right < 0
        dn_left = (left is None) or left < 0
        up_right = (right is None) or right > 0
        if up_left and down_right and not (left is None and right is None):
            maxima.append((a, b))
        if dn_left and up_right and not (left is None and right is None):
            minima.append((a, b))
    nz = rel[s != 0]
    return maxima, minima, (float(nz.min()) if len(nz) else float("nan"))


def interior_modes(P):
    mx, _, _ = modes(P)
    return [(a, b) for (a, b) in mx if a > 0 and b < len(P) - 1]


def sign_changes(P):
    d = np.diff(P)
    s = np.sign(d[d != 0])
    return int(np.sum(s[1:] != s[:-1]))


# ----------------------------------------------------------------------------- brute force

def brute(lp, lm, N, start):
    """Sum over all 2^N sign strings. start = +1, -1 (fresh) or ('nu', nu_p, nu_m)."""
    from itertools import product
    P = np.zeros(N + 1)
    for s in product((1, -1), repeat=N):
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
        for i, (sg, ln) in enumerate(runs):
            L = lp if sg > 0 else lm
            last = (i == len(runs) - 1)
            if i == 0:
                if start in (1, -1):
                    if sg != start:
                        pr = 0.0
                        break
                    pr *= L.T[ln] if last else L.f[ln]
                else:
                    _, nu_p, nu_m = start
                    nu = nu_p if sg > 0 else nu_m
                    pr *= nu[ln:].sum() if last else nu[ln]
            else:
                pr *= L.T[ln] if last else L.f[ln]
        if pr:
            P[sum(1 for x in s if x > 0)] += pr
    return P


if __name__ == "__main__":
    # self test against brute force
    for lp, lm in [(sibuya(0.4, 40), sibuya(0.7, 40)),
                   (geom_mix([0.9, 0.1], [0.1, 0.99], 40), zeta_law(0.6, 40))]:
        E = Engine(lp, lm, 14)
        for N in (1, 2, 5, 9, 12):
            for sg in (1, -1):
                err = np.abs(E.fresh(N, sg) - brute(lp, lm, N, sg)).max()
                assert err < 1e-14, (N, sg, err)
            nu_p = np.zeros(30)
            nu_m = np.zeros(30)
            nu_p[[2, 5, 7]] = [0.2, 0.1, 0.15]
            nu_m[[1, 4, 13]] = [0.3, 0.2, 0.05]
            err = np.abs(E.general(N, nu_p, nu_m) - brute(lp, lm, N, ("nu", nu_p, nu_m))).max()
            assert err < 1e-14, (N, "nu", err)
            assert abs(E.fresh(N, 1).sum() - 1) < 1e-13
    print("engine agrees with brute force for N <= 12, fresh and general starts")
