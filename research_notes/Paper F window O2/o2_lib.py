# o2_lib.py
# Problem 131, Paper F, window O2: shared routines.
# Exact occupation law P_N(k) of the lattice Levy walk (fresh plus start) by a
# recursion on (minus count, plus count); brute-force and forward Markov checks;
# the kernel G_N of eq:G; the profile h_N of eq:profile; the light-side
# exponent Lambda_N of the minus runs.
# Run with: py -I <script that imports this file>  (no network, no state).
import math
import numpy as np
from scipy.special import zeta as hz, gamma as Gfun
from scipy.optimize import brentq
from scipy.integrate import quad


class Law:
    """Run law on {1,2,...}: mixture (1-w)*delta_1 + w*zeta(alpha)."""

    def __init__(self, alpha, w=1.0):
        self.alpha, self.w = alpha, w
        self.z = float(hz(alpha + 1.0, 1.0))
        self.mu = (1.0 - w) + w * float(hz(alpha, 1.0)) / self.z

    def f(self, nmax):
        n = np.arange(nmax + 1, dtype=float)
        out = np.zeros(nmax + 1)
        out[1:] = self.w * n[1:] ** (-self.alpha - 1.0) / self.z
        if nmax >= 1:
            out[1] += 1.0 - self.w
        return out

    def T(self, nmax):
        """T(n) = P(X >= n) for n = 0..nmax, T(0) = 1."""
        n = np.arange(nmax + 1, dtype=float)
        out = np.ones(nmax + 1)
        out[2:] = self.w * hz(self.alpha + 1.0, n[2:]) / self.z
        return out

    def Tcont(self, x):
        """Hurwitz extension of T to real x > 1 (for the zeta part)."""
        return self.w * float(hz(self.alpha + 1.0, x)) / self.z

    def scale(self, t):
        """a(t) with t T(a) = 1 (Hurwitz extension of T); 1 if t*T(1+) <= 1."""
        lo = 1.0 + 1e-12
        if t * self.Tcont(lo) <= 1.0:
            return 1.0
        return brentq(lambda b: t * self.Tcont(b) - 1.0, lo, 1e12)

    def tail_const(self):
        """T(n) ~ c n^(-alpha)."""
        return self.w / (self.alpha * self.z)

    # ---- Laplace transform of the left tail -------------------------------
    def psi_and_dpsi(self, lam):
        """psi(l) = log E exp(-l (X - mu)), and psi'(l)."""
        M = int(min(max(80.0 / lam, 1000), 4e7))
        n = np.arange(1, M + 1, dtype=float)
        fn = self.w * n ** (-self.alpha - 1.0) / self.z
        fn[0] += 1.0 - self.w
        u = lam * n
        core = np.sum(fn * (u + np.expm1(-u)))          # E[e^{-lX}-1+lX], n <= M
        # tail n > M: e^{-lX} part is below e^{-80}; keep l X - 1 exactly
        tz1 = self.w * float(hz(self.alpha, M + 1.0)) / self.z
        tz0 = self.w * float(hz(self.alpha + 1.0, M + 1.0)) / self.z
        core += lam * tz1 - tz0
        phi1 = core                                       # E e^{-lX} - 1 + l mu
        psi = math.log1p(phi1 - lam * self.mu) + lam * self.mu
        e = np.exp(-u)
        Z = np.sum(fn * e)
        EX = np.sum(fn * n * e) / Z
        return psi, self.mu - EX

    def Lambda(self, m, d):
        """sup_{l>=0} [l d - m psi(l)] and the maximiser."""
        if d <= 0:
            return 0.0, 0.0
        if d >= 0.999 * m * (self.mu - 1.0):    # beyond (or at) the hard wall X >= 1
            return float('inf'), float('inf')
        g = lambda l: m * self.psi_and_dpsi(l)[1] - d
        lo, hi = 1e-9, 1e-3
        while g(hi) < 0:
            hi *= 2.0
            if hi > 50:
                raise ValueError("saddle out of range")
        lam = brentq(g, lo, hi, xtol=1e-14, rtol=1e-12)
        psi, _ = self.psi_and_dpsi(lam)
        return lam * d - m * psi, lam


def stable_light_const(alpha):
    """c_Z with P(Z <= -y) = exp(-c_Z y^beta (1+o(1))), E e^{itZ}=exp(K(-it)^alpha)."""
    K = -Gfun(1.0 - alpha)
    beta = alpha / (alpha - 1.0)
    return (alpha - 1.0) * alpha ** (-beta) * K ** (-1.0 / (alpha - 1.0)), beta


# ---- exact law -----------------------------------------------------------
def exact_law(N, lp, lm):
    """P_N(k), k = 0..N, fresh plus start, by the final-run identity.

    A[j, x]: a plus run starts after j minus steps and x plus steps (rho_j(x)).
    Bm[j, x]: a minus run starts after j minus steps and x plus steps.
    """
    fp, fm = lp.f(N + 1), lm.f(N + 1)
    Tp, Tm = lp.T(N + 1), lm.T(N + 1)
    A = np.zeros((N + 1, N + 1))
    Bm = np.zeros((N + 1, N + 1))
    P = np.zeros(N + 1)
    for j in range(0, N + 1):
        w = N - j                       # need x <= N - j
        if j == 0:
            A[0, 0] = 1.0
        else:
            A[j, :w + 1] = fm[j:0:-1] @ Bm[:j, :w + 1]
        # minus run starts after a complete plus run of length l >= 1
        Bm[j, :w + 1] = np.convolve(A[j, :w + 1], fp[:w + 1])[:w + 1]
        if j < N:
            k = N - j
            # final run plus: started at x plus steps, x <= k-1, length >= k - x
            P[k] += A[j, :k] @ Tp[k:0:-1]
    # final run minus: started after (N-j) plus and (j-m) minus steps, length >= m
    for j in range(1, N + 1):
        k = N - j
        m = np.arange(1, j + 1)
        P[k] += np.dot(Tm[m], Bm[j - m, k])
    return P


def brute_law(N, lp, lm):
    fp, fm = lp.f(N + 1), lm.f(N + 1)
    Tp, Tm = lp.T(N + 1), lm.T(N + 1)
    P = np.zeros(N + 1)

    def rec(rem, plus, count, prob):
        Tt = Tp if plus else Tm
        ff = fp if plus else fm
        P[count + (rem if plus else 0)] += prob * Tt[rem]
        for l in range(1, rem):
            rec(rem - l, not plus, count + (l if plus else 0), prob * ff[l])

    rec(N, True, 0, 1.0)
    return P


def markov_law(N, lp, lm):
    """Forward recursion on (count, sign, age); age = steps in current run."""
    Tp, Tm = lp.T(N + 2), lm.T(N + 2)
    hp = np.where(Tp[:-1] > 0, Tp[1:] / Tp[:-1], 0.0)   # P(len >= a+1 | len >= a)
    hm = np.where(Tm[:-1] > 0, Tm[1:] / Tm[:-1], 0.0)
    Sp = np.zeros((N + 1, N + 2))   # [count, age]
    Sm = np.zeros((N + 1, N + 2))
    Sp[1, 1] = 1.0                   # after step 1: plus run of age 1
    for t in range(1, N):
        nSp = np.zeros_like(Sp)
        nSm = np.zeros_like(Sm)
        a = np.arange(1, t + 1)
        # continue
        nSp[1:, 2:t + 2] += Sp[:-1, 1:t + 1] * hp[a]
        nSm[:, 2:t + 2] += Sm[:, 1:t + 1] * hm[a]
        # switch
        endp = (Sp[:, 1:t + 1] * (1 - hp[a])).sum(axis=1)
        endm = (Sm[:, 1:t + 1] * (1 - hm[a])).sum(axis=1)
        nSm[:, 1] += endp
        nSp[1:, 1] += endm[:-1]
        Sp, Sm = nSp, nSm
    return Sp.sum(axis=1) + Sm.sum(axis=1)


# ---- kernel and profile ---------------------------------------------------
def renewal_u(f, J):
    u = np.zeros(J + 1)
    u[0] = 1.0
    for j in range(1, J + 1):
        u[j] = np.dot(f[1:j + 1], u[j - 1::-1])
    return u


class Setup:
    def __init__(self, N, lp, lm):
        self.N, self.lp, self.lm = N, lp, lm
        self.s = lp.mu + lm.mu
        self.p = lp.mu / self.s
        self.bp = lp.scale(N / self.s)
        self.bm = lm.scale(N / self.s)
        self.B = max(self.bp, self.bm)
        self.thp, self.thm = self.bp / self.B, self.bm / self.B
        self.um = renewal_u(lm.f(N + 1), N)
        c = np.convolve(self.um, self.um)[:N + 1]
        self.gam = np.concatenate([[0.0], np.cumsum(self.um)[:-1]]) + lp.mu * (c - self.um)
        self.gam[0] = 0.0
        self.fp, self.Tp = lp.f(N + 1), lp.T(N + 1)

    def G(self, k):
        N, p = self.N, self.p
        L = (k - p * N) / (1 - p)
        Li = int(math.floor(L))
        j = N - k
        return self.gam[j] * self.fp[Li] + self.Tp[Li] * self.um[j]

    def x_of(self, k):
        return (k - self.p * self.N) / self.B

    def h(self, x):
        ap, am = self.lp.alpha, self.lm.alpha
        cp, cm = (1 - self.p) * self.thp, self.p * self.thm
        # T(n) ~ c n^-alpha with a(t): t T(a)=1 gives Z with E e^{itZ}=exp(K(-it)^alpha)
        Kp, Km = -Gfun(1 - ap), -Gfun(1 - am)

        def phi(t):
            return np.exp(Kp * (-1j * cp * t) ** ap + Km * (1j * cm * t) ** am)

        re = quad(lambda t: phi(t).real, 0, np.inf, weight='cos', wvar=x, limlst=200)[0]
        im = quad(lambda t: phi(t).imag, 0, np.inf, weight='sin', wvar=x, limlst=200)[0]
        return (re + im) / math.pi

    def tau(self, x):
        ap = self.lp.alpha
        return ap * ((1 - self.p) * self.thp) ** ap * x ** (-ap - 1)

    def LambdaN(self, x):
        """Lambda_N(x) = Lambda^-_{N/s}((x/p) B_N)."""
        return self.lm.Lambda(self.N / self.s, (x / self.p) * self.B)[0]


def Lambda_tilde(S, k):
    """Finite-N light exponent at the run count that keeps the plus runs typical:
    Lambda^-_m(m mu_- - j) with m = k / mu_+ and j = N - k."""
    m = k / S.lp.mu
    j = S.N - k
    return S.lm.Lambda(m, m * S.lm.mu - j)[0]
