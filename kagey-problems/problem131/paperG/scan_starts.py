"""General initial runs for 0 < alpha < 1, and the degenerate case alpha = alpha_c.

Run with `py -I scan_starts.py [Nmax]`.  Sibuya laws for both signs (b = 1).

(A) A point-mass minus run of length d0 with probability 1/2 (F's prepared start): two
    local maxima in the plus-end profile, so the predicted count rises by one.
(B) A smooth heavy initial run nu_+(n) ~ n^{-1-gamma}, gamma = 0.2: satisfies the difference
    condition (S1); predicted count unchanged (the atom at N is then a mode).
(C) Oscillating initial runs that satisfy every hypothesis of G's Conjecture conj:count
    (local law, W = o(T), finite kappa(0) limits, eventually decreasing profiles):
      alpha >= 1/2: nu_+(n) = c n^{-1-alpha} (1 + eps (-1)^n), eps = 0.9,
      alpha <  1/2: nu_+(n) = c (n^{-1-alpha} + lam (-1)^n n^{alpha-2}), lam = 0.3,
    rest of the mass at d = 1.  Prediction: the count grows without bound, with the extra
    extrema packed around the critical points of L.
(D) alpha = alpha_c (degenerate minimum of L at 1/2).
"""
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from shape_engine import Engine, sibuya, modes
from scan_alpha_lt1 import profile_maxima
from lamperti_critical import beta_c

DMAX = 2_000_000


def show(label, P, pred=None):
    mx, mn, gap = modes(P)
    N = len(P) - 1
    tag = "" if pred is None else ("  predicted %d%s" % (pred, "" if len(mx) == pred else "  <-- differs"))
    if len(mx) <= 12:
        loc = [a if a == b else (a, b) for a, b in mx]
    else:
        xs = np.array([a for a, b in mx]) / N
        loc = "spread over x in [%.3f, %.3f]; histogram (10 bins on [0,1]): %s" % (
            xs.min(), xs.max(), np.histogram(xs, bins=10, range=(0, 1))[0].tolist())
    print("    %s N=%5d modes=%d %s min rel gap %.1e%s" % (label, N, len(mx), loc, gap, tag))
    return len(mx)


def nu_arrays(kind, alpha):
    n = np.arange(DMAX + 1, dtype=float)
    nu_p = np.zeros(DMAX + 1)
    nu_m = np.zeros(DMAX + 1)
    if kind == "smooth":
        g = 0.2
        nu_p[2:] = n[2:] ** (-1 - g)
        nu_p[2:] *= 0.5 / nu_p[2:].sum()
        nu_p[1] = 0.5
    elif kind == "osc_hi":  # alpha >= 1/2
        eps = 0.9
        nu_p[2:] = n[2:] ** (-1 - alpha) * (1 + eps * (-1) ** n[2:].astype(int))
        nu_p[2:] *= 0.5 / nu_p[2:].sum()
        nu_p[1] = 0.5
    elif kind == "osc_lo":  # alpha < 1/2
        base = n[2:] ** (-1 - alpha)
        alt = (-1) ** n[2:].astype(int) * n[2:] ** (alpha - 2)
        lam = 0.3  # base dominates alt pointwise since n^{-1-alpha} >= n^{alpha-2}
        nu_p[2:] = base + lam * alt
        nu_p[2:] *= 0.5 / nu_p[2:].sum()
        nu_p[1] = 0.5
    # the mass beyond DMAX is put on d = 1 implicitly by normalising to total mass 1
    s = nu_p.sum() + nu_m.sum()
    nu_p[1] += 1.0 - s
    return nu_p, nu_m


def kappa_minus_check(nu_p, up, J=3000):
    """Profile at the minus end: kappa_-(j) = pi_- u_+(j) + (nu_+ * u_+)(j), pi_- = 0 here.
    Return the last j <= J with a nonnegative difference (eventual strict decrease)."""
    k = np.convolve(nu_p[:J + 1], up[:J + 1])[:J + 1]
    d = np.diff(k[1:])
    nz = np.where(d >= 0)[0]
    return (int(nz[-1]) + 2) if len(nz) else 1


if __name__ == "__main__":
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    Ns = [n for n in (500, 1000, 1500, 2000, 2500, 3000, 4000) if n <= Nmax]
    n0 = Nmax + 5
    for a in (0.7, 0.3):
        L = sibuya(a, n0)
        E = Engine(L, L, Nmax)
        u = L.renewal(3000)
        mL = 1 if beta_c(a) > 0 else 0
        print("\n== Sibuya(%g) both signs, m_L = %d" % (a, mL))
        # (A) prepared start
        d0 = 3
        nu_p = np.zeros(Nmax + 2)
        nu_m = np.zeros(Nmax + 2)
        nu_m[d0] = 0.5
        nu_p[:len(L.f)] = 0.5 * L.f[:Nmax + 2]
        nu_p[-1] = 0.5 * L.T[Nmax + 1]  # tail mass of the fresh plus half, as D >= Nmax+1
        kp = np.zeros(3001)
        kp[1:] = 0.5 * u[1:3001]
        kp[d0:] += 0.5 * u[:3001 - d0]
        kp[0] = 0.5
        Mp = len(modes(kp[:200])[0])
        Mm, _, _, _ = profile_maxima(0.0, u)
        # minus-end profile: pi_- u_+(j) + nu_+ * u_+ = 0.5 u(j) + 0.5 (f * u)(j) = u(j) - 0.5 delta
        km = 0.5 * u[:3001] + 0.5 * np.convolve(L.f[:3001], u[:3001])[:3001]
        km[0] = 0.0  # Q_-(N) = 0 for N > d0
        Mm = len(modes(km[:200])[0])
        print("  (A) half fresh plus, half minus run of length %d: profile maxima %d + %d"
              % (d0, Mp, Mm))
        for N in Ns:
            show("(A)", E.general(N, nu_p, nu_m), Mp + Mm + mL)
        # (B) smooth heavy start
        nu_p, nu_m = nu_arrays("smooth", a)
        print("  (B) nu_+(n) ~ n^-1.2 (atom at N dominates), nu_+(1) = %.3f" % nu_p[1])
        for N in Ns:
            show("(B)", E.general(N, nu_p, nu_m), 1 + 1 + mL)
        # (C) oscillating start
        kind = "osc_hi" if a >= 0.5 else "osc_lo"
        nu_p, nu_m = nu_arrays(kind, a)
        Jm = kappa_minus_check(nu_p, u)
        QT = [nu_p[N:].sum() / L.T[N] for N in (1000, 2000, 3000) if N <= Nmax]
        print("  (C) %s: minus-end profile strictly decreasing from j = %d; Q_+(N)/T(N) = %s;"
              " N nu_+(N) at N = 3000: %.2e" % (kind, Jm, ["%.4f" % q for q in QT],
                                               3000 * nu_p[3000]))
        for N in Ns:
            show("(C)", E.general(N, nu_p, nu_m), 1 + 1 + mL)
        del E
    # (D) alpha_c
    from scipy.optimize import brentq
    ac = brentq(lambda a: math.cos(math.pi * a / 2) - a, 0.1, 0.9)
    for a in (ac, ac - 0.005, ac + 0.005):
        L = sibuya(a, n0)
        E = Engine(L, L, Nmax)
        print("\n== (D) Sibuya(%.6f) both signs, fair and fresh plus start" % a)
        for N in Ns:
            show("fair ", E.fair(N))
            show("plus ", E.fresh(N, 1))
        del E
