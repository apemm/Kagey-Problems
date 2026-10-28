"""The numbers of Sections sec:lamperti and sec:shape on the Lamperti density.

  1. The root of cos(pi a/2) = a in (0, 1) is 0.5946116441 (10 digits), and the identity
     1 + cos(pi a) - 2 a^2 = 2 (cos(pi a/2) - a)(cos(pi a/2) + a) holds on a grid.
  2. On a grid of 2*10^5 + 1 points of (0, 1), L_{a,1} has 1 critical point for a = 0.3, 0.5, 0.55,
     0.59, 0.5946 and 3 for a = 0.5947, 0.6, 0.7, 0.8, 0.9, 0.95. This agrees with the value 0.5946
     of Margolin and Barkai.
  3. The function G(t) = cosh(a t) - a sinh(a t) coth(t/2) of the proof of thm:shape is increasing on
     a grid of (0, 20] for a = 0.1, 0.3, ..., 0.9, with G(0+) = 1 - 2 a^2.
  3b. Proposition prop:pitchfork: the zero t* of chi is 0.0790 at a = 0.5947 and 1.018 at a = 0.61,
     the first expression of the proposition is within 0.01% and 1.5% of it, and at a = 0.61 the
     minimum of L sits at x = 0.2655.
  4. For b != 1 (not covered by thm:shape): at a = 0.7 the number of critical points is 3 for
     b = 1, 2 and 1 for b = 3.
  5. The transform (eq:stieltjes) of prop:lambda: int_0^1 L_{a,b}(v)/(1 + s v) dv equals
     ((1+s)^(a-1) + b)/((1+s)^a + b) to 1e-25 (30-digit arithmetic) for a = 0.3, 0.5, 0.8, b = 0.5, 1, 3, s = -0.5, 0, 1, 4.
     At s = 0 this is the total mass 1, and the mean of L_{a,b} is 1/(1+b).
  6. The double integral Lambda of thm:local at a = 1/2 equals L(x) at x = 0.2, 0.5, 0.7 to 1e-13
     (relative), with g the positive 1/2-stable density with Laplace transform exp(-sqrt(pi l)).

Run from the paper folder:  py -I verify_shape.py
Output: data/verify_shape_output.txt (with the sha256 of this script and the date).
Exit status 1 if any check fails.
"""
import importlib.util
import sys
import time
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("lamperti_law", HERE / "lamperti_law.py")
lw = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lw)

R = lw.Report(__file__)


def critical_points(a, b=1.0):
    x = np.linspace(1e-4, 1 - 1e-4, 200001)
    return lw.sign_changes(lw.lamperti(x, a, b))[0]


def main():
    t0 = time.time()
    R.log("verify_shape.py: the Lamperti density")

    ac = brentq(lambda a: np.cos(np.pi * a / 2) - a, 0.3, 0.9, xtol=1e-15)
    R.log(f"   root of cos(pi a/2) = a: {ac:.15f}")
    grid = np.linspace(0.001, 0.999, 999)
    ident = np.max(np.abs(1 + np.cos(np.pi * grid) - 2 * grid ** 2
                          - 2 * (np.cos(np.pi * grid / 2) - grid) * (np.cos(np.pi * grid / 2) + grid)))
    R.check("1. threshold 0.5946116441 and the factorization of 1 + cos(pi a) - 2a^2",
            f"{ac:.10f}" == "0.5946116441" and ident < 1e-12, f"{ac:.12f}, identity error {ident:.1e}")

    below = (0.3, 0.5, 0.55, 0.59, 0.5946)
    above = (0.5947, 0.6, 0.7, 0.8, 0.9, 0.95)
    cb = [critical_points(a) for a in below]
    ca = [critical_points(a) for a in above]
    R.log("   critical points of L_{a,1}: " + ", ".join(f"a={a}: {n}" for a, n in zip(below + above, cb + ca)))
    R.check("2. one critical point below the threshold and three above it", all(n == 1 for n in cb)
            and all(n == 3 for n in ca))

    mono = True
    for a in (0.1, 0.3, 0.5, 0.7, 0.9):
        t = np.linspace(1e-3, 20, 20000)
        G = np.cosh(a * t) - a * np.sinh(a * t) / np.tanh(t / 2)
        mono &= bool(np.all(np.diff(G) > 0)) and abs(G[0] - (1 - 2 * a * a)) < 1e-5
    R.check("3. G increasing on (0, 20] with G(0+) = 1 - 2a^2", mono)

    out = {}
    for a in (0.5947, 0.61):
        chi = lambda t: np.cosh(a * t) + np.cos(np.pi * a) - a * np.sinh(a * t) / np.tanh(t / 2)
        ts = brentq(chi, 1e-6, 50, xtol=1e-14)
        pred = np.sqrt(3 * (2 * a * a - 1 - np.cos(np.pi * a)) / (a * a * (1 - a * a)))
        out[a] = (ts, abs(pred / ts - 1), 1 / (1 + np.exp(ts)))
        R.log(f"   a = {a}: t* = {ts:.6f}, prediction {pred:.6f}, relative error {abs(pred / ts - 1):.2e}, "
              f"minimum at x = {1 / (1 + np.exp(ts)):.4f}")
    R.check("3b. prop:pitchfork: t* = 0.0790 within 0.01% (a = 0.5947), t* = 1.018 within 1.5% and minimum at "
            "x = 0.2655 (a = 0.61)",
            f"{out[0.5947][0]:.4f}" == "0.0790" and out[0.5947][1] < 1e-4 and f"{out[0.61][0]:.3f}" == "1.018"
            and out[0.61][1] < 0.015 and f"{out[0.61][2]:.4f}" == "0.2655")

    nb = {b: critical_points(0.7, b) for b in (1.0, 2.0, 3.0)}
    R.log("   a = 0.7: critical points of L_{a,b}: " + ", ".join(f"b={b:g}: {n}" for b, n in nb.items()))
    R.check("4. a = 0.7: 3 critical points for b = 1, 2 and 1 for b = 3", nb == {1.0: 3, 2.0: 3, 3.0: 1})

    # 5. in 30-digit arithmetic, with v = t^(1/a) on (0, 1/2] and 1 - v = t^(1/a) on [1/2, 1), which
    # removes the endpoint singularities of L
    mp.mp.dps = 30

    def Lr(v, w, a, b):            # L_{a,b} without the factor v^(a-1) w^(a-1), w = 1 - v
        c = mp.cos(mp.pi * a)
        return mp.sin(mp.pi * a) / mp.pi * b / (b * b * v ** (2 * a) + 2 * b * c * v ** a * w ** a + w ** (2 * a))

    def integral(g, a, b):         # int_0^1 L_{a,b}(v) g(v) dv
        m = (mp.mpf(1) / 2) ** a
        left = mp.quad(lambda t: Lr(t ** (1 / a), 1 - t ** (1 / a), a, b) * (1 - t ** (1 / a)) ** (a - 1)
                       * g(t ** (1 / a)) / a, [0, m])
        right = mp.quad(lambda t: Lr(1 - t ** (1 / a), t ** (1 / a), a, b) * (1 - t ** (1 / a)) ** (a - 1)
                        * g(1 - t ** (1 / a)) / a, [0, m])
        return left + right

    worst = mp.mpf(0)
    wmean = mp.mpf(0)
    for a in (mp.mpf(3) / 10, mp.mpf(1) / 2, mp.mpf(4) / 5):
        for b in (mp.mpf(1) / 2, mp.mpf(1), mp.mpf(3)):
            for s in (-mp.mpf(1) / 2, mp.mpf(0), mp.mpf(1), mp.mpf(4)):
                lhs = integral(lambda v: 1 / (1 + s * v), a, b)
                rhs = ((1 + s) ** (a - 1) + b) / ((1 + s) ** a + b)
                worst = max(worst, abs(lhs - rhs))
            wmean = max(wmean, abs(integral(lambda v: v, a, b) - 1 / (1 + b)))
    R.check("5. the transform eq:stieltjes and the mean 1/(1+b)", worst < 1e-25 and wmean < 1e-25,
            f"max error {mp.nstr(worst, 3)}, mean error {mp.nstr(wmean, 3)}")

    a = 0.5

    def g(z):
        return 0.0 if z <= 0 else 0.5 * z ** -1.5 * np.exp(-np.pi / (4 * z))

    def p(t, z):
        return g(z / t ** 2) / t ** 2

    def Q(t, x):
        return quad(lambda z: p(t, z), 0, x, weight="alg", wvar=(0, -a), limit=200)[0]

    rel = []
    for x in (0.2, 0.5, 0.7):
        y = 1 - x
        val = quad(lambda t: p(t, y) * Q(t, x) + p(t, x) * Q(t, y), 0, np.inf, limit=200)[0]
        rel.append(abs(val / lw.lamperti(x, a) - 1))
        R.log(f"   a = 1/2, x = {x}: Lambda = {val:.12f}, L = {lw.lamperti(x, a):.12f}")
    R.check("6. Lambda = L at a = 1/2", max(rel) < 1e-13, f"max relative difference {max(rel):.1e}")
    sys.exit(R.write(time.time() - t0))


if __name__ == "__main__":
    main()
