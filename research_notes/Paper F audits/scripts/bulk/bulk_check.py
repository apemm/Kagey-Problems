"""Check B_N P_N(k) against h_N((k-pN)/B_N) for zeta laws alpha_+=1.5, alpha_-=1.7, fresh plus start.

The recursion is a copy of occupation() in paperF/certify_atlas.py (unchanged logic, separate plus/minus laws).
h_N by Fourier inversion of phi(t)=exp(K+((1-p)th+)^a+(-it)^a+ + K-(p th-)^a-(it)^a-).
"""
import sys
import time
import numpy as np
from scipy.special import zeta, gamma
from scipy.integrate import quad
from scipy.optimize import brentq

AP, AM = 1.5, 1.7


def law(alpha, nmax):
    z = zeta(alpha + 1)
    n = np.arange(1, nmax + 1, dtype=float)
    f = np.concatenate([[0.0], n ** (-alpha - 1) / z])
    T = np.concatenate([[1.0], zeta(alpha + 1, n) / z])   # T(n)=P(X>=n)
    return f, T


def occupation(N, f, T, fm, Tm):
    B = np.zeros((N, N))
    P = np.zeros(N + 1)
    fm_rev = fm[N:0:-1].copy()
    for m in range(N):
        n = N - m
        if m == 0:
            a = np.zeros(n)
            a[0] = 1.0
        else:
            a = fm_rev[N - m:] @ B[:m, :n]
        P[N - m] += a @ T[n:0:-1]
        b = np.convolve(a, f[:n])[:n]
        B[m, :n] = b
        P[:n] += b * Tm[n:0:-1]
    return P


def K(alpha):
    return -gamma(1 - alpha)


def a_asym(alpha, t):
    # T(x) ~ x^-alpha/(alpha zeta(alpha+1)); t T(a(t)) -> 1
    return (t / (alpha * zeta(alpha + 1))) ** (1 / alpha)


def a_exact(alpha, t):
    # inverse of the continuous tail Tc(x) = zeta(alpha+1, x)/zeta(alpha+1) (Hurwitz, x>=1): t Tc(a) = 1
    z = zeta(alpha + 1)
    return brentq(lambda x: t * zeta(alpha + 1, x) / z - 1.0, 1.0, 1e12)


def h(x, thp, thm, p):
    cp = K(AP) * ((1 - p) * thp) ** AP
    cm = K(AM) * (p * thm) ** AM

    def re_phi(t):
        e = cp * (-1j * t) ** AP + cm * (1j * t) ** AM
        return (np.exp(e) * np.exp(-1j * t * x)).real

    v, _ = quad(re_phi, 0, np.inf, limit=400, epsabs=1e-12)
    return v / np.pi


def main():
    Ns = [int(a) for a in sys.argv[1:]] or [1000, 2000, 4000]
    mup = zeta(AP) / zeta(AP + 1)
    mum = zeta(AM) / zeta(AM + 1)
    s = mup + mum
    p = mup / s
    print(f"mu+={mup:.6f} mu-={mum:.6f} s={s:.6f} p={p:.6f}")
    for N in Ns:
        t0 = time.time()
        f, T = law(AP, N + 1)
        fm, Tm = law(AM, N + 1)
        P = occupation(N, f, T, fm, Tm)
        rt = time.time() - t0
        for name, afun in (("asym", a_asym), ("exact", a_exact)):
            bp, bm = afun(AP, N / s), afun(AM, N / s)
            BN = max(bp, bm)
            thp, thm = bp / BN, bm / BN
            k0 = int(round(p * N))
            x0 = (k0 - p * N) / BN
            lhs = BN * P[k0]
            rhs = h(x0, thp, thm, p)
            # sup over a window |x|<=3 on a grid of bins
            ks = np.arange(max(0, int(p * N - 3 * BN)), min(N, int(p * N + 3 * BN)) + 1)
            ks = ks[:: max(1, len(ks) // 60)]
            diffs = [abs(BN * P[k] - h((k - p * N) / BN, thp, thm, p)) for k in ks]
            hmax = max(h((k - p * N) / BN, thp, thm, p) for k in ks)
            hpin = (s / mum) * 0  # placeholder
            # pinned limit (theta_- = 0): (s/mu-) g+(s x/mu-)
            hlim = h(x0, 1.0, 0.0, p)
            print(f"N={N} [{name}] b+={bp:.3f} b-={bm:.3f} th-={thm:.4f} mass={P.sum():.12f} "
                  f"B_N P_N(k0)={lhs:.6f} h_N(x0)={rhs:.6f} ratio={lhs/rhs:.5f} "
                  f"h_pinned(x0)={hlim:.6f} sup|diff| on grid={max(diffs):.5f} (max h {hmax:.4f}) t={rt:.1f}s",
                  flush=True)


if __name__ == "__main__":
    main()
