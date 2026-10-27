"""Eventual mode count for 0 < alpha < 1: computed count against M_+ + M_- + m_L.

Run with `py -I scan_alpha_lt1.py [Nmax]`.  M_+ and M_- are the numbers of local maxima of
the end profiles (computed on 0 <= j <= 3000, where u is checked to be strictly decreasing
from J_+ on), and m_L = 1 iff L_{alpha,b} is W-shaped (lamperti_critical.beta_c).
"""
import math
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from shape_engine import Engine, sibuya, zeta_law, geom_mix, mix, modes
from lamperti_critical import beta_c


def profile_maxima(c0, u, nu_other=None, pi_same=None):
    """Local maxima of (c0, kappa(1), kappa(2), ...), kappa = pi u + nu * u on j >= 1."""
    J = len(u) - 1
    if nu_other is None:
        kap = u.copy()
    else:
        kap = pi_same * u.copy()
        conv = np.convolve(nu_other[:J + 1], u)[:J + 1]
        kap = kap + conv
    y = kap.copy()
    y[0] = c0
    d = np.diff(y)
    # eventual strict decrease and the last index of a non-negative difference
    nonneg = np.where(d >= 0)[0]
    Jlast = int(nonneg[-1]) + 1 if len(nonneg) else 0
    ties = np.where(d == 0)[0]
    mx, _, _ = modes(y[: max(Jlast + 50, 60)])
    return len(mx), [a for a, b in mx], Jlast, len(ties)


def run_case(name, lp, lm, alpha, b, starts, Ns, Nmax):
    t0 = time.time()
    E = Engine(lp, lm, Nmax)
    up = lp.renewal(3000)
    um = lm.renewal(3000)
    bc = beta_c(alpha)
    mL = 1 if abs(math.log(b)) < bc else 0
    print("\n== %s   alpha=%.4g  b=%.4g  |log b|=%.3f  beta_c=%.3f  m_L=%d   (%.0fs)"
          % (name, alpha, b, abs(math.log(b)), bc, mL, time.time() - t0))
    for st in starts:
        if st == "plus":
            cp, cm = 1.0, 0.0
        elif st == "minus":
            cp, cm = 0.0, 1.0
        else:
            cp, cm = 0.5, 0.5
        Mp, locp, Jp, tp = profile_maxima(cp, um)
        Mm, locm, Jm, tm = profile_maxima(cm, up)
        pred = Mp + Mm + mL
        row = []
        for N in Ns:
            P = E.fresh(N, 1) if st == "plus" else E.fresh(N, -1) if st == "minus" else E.fair(N)
            mx, mn, gap = modes(P)
            row.append((N, len(mx), mx, mn, gap))
        print("  start %-5s profile maxima: plus end j=%s (J=%d), minus end j=%s (J=%d); "
              "predicted %d" % (st, locp, Jp, locm, Jm, pred))
        for N, c, mx, mn, gap in row:
            flag = "" if c == pred else "   <-- differs"
            mxs = [a if a == bb else (a, bb) for a, bb in mx]
            mns = [a if a == bb else (a, bb) for a, bb in mn]
            print("    N=%5d  modes=%d %s  minima=%s  min rel gap=%.1e%s"
                  % (N, c, mxs, mns, gap, flag))


if __name__ == "__main__":
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    Ns = [n for n in (250, 500, 1000, 1500, 2000, 2500, 3000, 4000) if n <= Nmax]
    n = Nmax + 5
    G = lambda a: math.gamma(1 - a)
    # 1. Sibuya, b = 1
    for a in (0.3, 0.5, 0.65, 0.7, 0.9):
        L = sibuya(a, n)
        run_case("Sibuya(%g) both signs" % a, L, L, a, 1.0, ("plus", "fair"), Ns, Nmax)
    # 2. unequal weights, same index: minus = p Sibuya + (1-p) geometric(0.5)
    for a, p in ((0.7, 0.6), (0.7, 0.25), (0.8, 0.05), (0.65, 0.5)):
        Lp = sibuya(a, n)
        Lm = mix([sibuya(a, n), geom_mix([1.0], [0.5], n)], [p, 1 - p],
                 "%.2f Sib + %.2f geom" % (p, 1 - p))
        run_case("plus Sibuya(%g), minus %s" % (a, Lm.name), Lp, Lm, a, p,
                 ("plus", "minus", "fair"), Ns, Nmax)
    # 3. runs of length at least two (several profile maxima)
    a = 0.7
    L = zeta_law(a, n, start=2)
    from scipy.special import zeta
    run_case("zeta(0.7) on n>=2, both signs", L, L, a, 1.0, ("plus", "fair"), Ns, Nmax)
