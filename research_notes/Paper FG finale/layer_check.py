"""Checks of the layer and bulk difference statements for 0 < alpha < 1.

Run with `py -I layer_check.py [Nmax]`.  Sibuya laws, b = 1.
(1) Theorem L: D_N(j) = P_N(N-j-1) - P_N(N-j) against T_+(N) (u_-(j+1) - u_-(j)), for the
    fresh plus, fresh minus and fair starts.  The ratio should tend to 1 for j fixed large,
    with an error of relative order (j/N)^alpha + j/N.
(2) DSRT: j (u(j) - u(j+1)) / u(j) -> 1 - alpha (Sibuya: u(j) = Gamma(j+alpha)/(Gamma(alpha) j!),
    so u(j+1)/u(j) = (j+alpha)/(j+1) exactly and j(1 - u(j+1)/u(j)) = j(1-alpha)/(j+1)).
(3) Theorem B: N^2 (P_N(k+1) - P_N(k)) against L'(k/N).
"""
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from shape_engine import Engine, sibuya


def L(x, a, b=1.0):
    c = math.cos(math.pi * a)
    return (math.sin(math.pi * a) / math.pi * b * x ** (a - 1) * (1 - x) ** (a - 1)
            / (b * b * x ** (2 * a) + 2 * b * c * x ** a * (1 - x) ** a + (1 - x) ** (2 * a)))


def dL(x, a, h=1e-6):
    return (L(x + h, a) - L(x - h, a)) / (2 * h)


if __name__ == "__main__":
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    for a in (0.3, 0.7):
        lw = sibuya(a, Nmax + 5)
        E = Engine(lw, lw, Nmax)
        u = lw.renewal(Nmax)
        du = np.diff(u)
        print("\n== Sibuya(%g), both signs" % a)
        print("  DSRT: j(u(j)-u(j+1))/u(j) at j = 10, 100, 1000:",
              ["%.4f" % (j * -du[j] / u[j]) for j in (10, 100, 1000)], " (1 - alpha = %.2f)" % (1 - a))
        js = (5, 20, 50, 100, 200, 400, 800)
        for N in (1000, 3000):
            if N > Nmax:
                continue
            for st in ("plus", "minus", "fair"):
                P = E.fresh(N, 1) if st == "plus" else E.fresh(N, -1) if st == "minus" else E.fair(N)
                rat = [(P[N - j - 1] - P[N - j]) / (lw.T[N] * du[j]) for j in js]
                print("  N=%d %-5s D_N(j)/(T(N) du(j)) at j=%s: %s"
                      % (N, st, js, " ".join("%.3f" % r for r in rat)))
        for N in (1000, 3000):
            if N > Nmax:
                continue
            P = E.fair(N)
            xs = (0.2, 0.3, 0.4, 0.45)
            vals = [N * N * (P[int(x * N) + 1] - P[int(x * N)]) for x in xs]
            print("  N=%d fair: N^2 dP at x=%s: %s ; L'(x): %s"
                  % (N, xs, " ".join("%.3f" % v for v in vals),
                     " ".join("%.3f" % dL(x, a) for x in xs)))
        del E
