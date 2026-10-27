"""Unequal and mixed indices: the shape of the limit law of the dominated count.

Run with `py -I mixed_index.py [Nmax]`.

Plus runs heavier: alpha_+ < alpha_-, alpha_+ < 1.  The number of minus steps j = N - A_N lives
on the scale Lambda_N = a_-(1/T_+(N)) (alpha_- < 1) or mu_-/T_+(N) (alpha_- > 1), and
    j / Lambda_N  ->  W = Z_+^{-alpha_+/alpha_-} Z_-     (alpha_- < 1),
    j T_+(N)/mu_- ->  xi = Z_+^{-alpha_+}                 (alpha_- > 1, Mittag-Leffler law),
with Z_+, Z_- independent positive stable, E exp(-l Z) = exp(-l^alpha).  Mellin transform:
    E W^s = Gamma(1-s/a_-) Gamma(1+s/a_-) / (Gamma(1-s) Gamma(1+g s)),  g = a_+/a_-,
for -a_- < s < a_-.  For a_+ = a_- = a this is sin(pi s)/(a sin(pi s/a)), the Mellin transform
of the ratio density K_a(w) = (sin pi a / pi) w^{a-1}/(w^{2a} + 2 w^a cos pi a + 1).

Part 1: the density h of W by Mellin inversion on Re s = 0, and the number of sign changes
of h' on (0, infinity): 0 (decreasing) or 2 (one interior mode).  Threshold curve in
(alpha_-, alpha_+).
Part 2: the Mittag-Leffler density f of xi, by the same Mellin inversion (alpha_- = 1);
f(x) = sum_k (-x)^k / (k! Gamma(1 - a - a k)), so f'(0) = -1/Gamma(1-2a), positive iff a > 1/2.
Part 3: exact laws (Sibuya runs) for (alpha_+, alpha_-) = (0.75, 0.95), (0.3, 0.9), and the
mixed pairs Sibuya(0.7), Sibuya(0.4) / zeta(1.5); modes of P_N, and a check of the bulk
formula (one giant minus run, either in progress at time N or completed):
    P_N(xN) ~ (sin(pi a_+)/pi) (T_-(N) / (N T_+(N))) G(x),
    G(x) = x^{a_+-1} (1-x)^{-a_- - 1} ((1-x) + (a_-/a_+) x),
whose unique critical point x* (a minimum) solves the quadratic
    (a_+-1)(1-x)(1+(r-1)x) + (a_-+1) x (1+(r-1)x) + (r-1) x (1-x) = 0,  r = a_-/a_+.
"""
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from scipy.special import loggamma, gamma as G

def tau_grid(ap, am, dt=0.02):
    rate = (math.pi / (2 * am)) * (2 - am - ap)   # |M(i tau)| ~ |tau|^c exp(-rate |tau|)
    tmax = min(45.0 / rate, 3000.0)
    return np.arange(-tmax, tmax + dt / 2, dt)


def logM(s, ap, am):
    g = ap / am
    return (loggamma(1 - s / am) + loggamma(1 + s / am) - loggamma(1 - s) - loggamma(1 + g * s))


def h_and_dh(w, ap, am, sigma=0.0, chunk=40):
    """h(w) and w^2 h'(w) by Mellin inversion along Re s = sigma (|sigma| < alpha_-)."""
    tau = tau_grid(ap, am)
    s = sigma + 1j * tau
    M = np.exp(logM(s, ap, am))
    dt = tau[1] - tau[0]
    H = np.zeros(len(w))
    D = np.zeros(len(w))
    for i in range(0, len(w), chunk):
        ww = w[i:i + chunk]
        kern = np.exp(-(s[None, :]) * np.log(ww)[:, None]) * M[None, :]   # w^{-s} M(s)
        H[i:i + chunk] = (kern.sum(axis=1) * dt).real / (2 * np.pi) / ww
        D[i:i + chunk] = (((-(s[None, :] + 1)) * kern).sum(axis=1) * dt).real / (2 * np.pi)
    return H, D   # D = w^2 h'(w)


def sign_changes(v, rel=1e-9):
    v = np.asarray(v)
    scale = np.abs(v).max()
    s = np.sign(np.where(np.abs(v) < rel * scale, 0, v))
    s = s[s != 0]
    return int(np.sum(s[1:] != s[:-1]))


if __name__ == "__main__":
    W = np.exp(np.linspace(np.log(1e-4), np.log(1e4), 401))
    # sanity: equal indices reproduce K_a
    for a in (0.5, 0.8):
        h, _ = h_and_dh(W, a, a)
        K = math.sin(math.pi * a) / math.pi * W ** (a - 1) / (W ** (2 * a) + 2 * W ** a * math.cos(math.pi * a) + 1)
        sel = (W > 1e-2) & (W < 1e2)
        print("check a=%.2f: max |h - K_a| / K_a on [1e-2,1e2] = %.2e" % (a, np.max(np.abs(h[sel] - K[sel]) / K[sel])))
    # Part 1
    print("\nPart 1. interior mode of h (sign changes of h' = 2) for alpha_+ <= alpha_- < 1")
    print("alpha_-  smallest alpha_+ (step 0.01) with an interior mode")
    curve = []
    for am in (0.6, 0.7, 0.74, 0.76, 0.8, 0.85, 0.9, 0.95, 0.98):
        found = None
        for ap in np.arange(0.05, am + 1e-9, 0.01):
            _, dh = h_and_dh(W, ap, am)
            sc = sign_changes(dh)
            if sc >= 2:
                found = (ap, sc)
                break
        curve.append((am, found))
        print("  %.2f    %s" % (am, "none (h decreasing for every alpha_+ <= alpha_-)" if found is None
                                 else "%.2f   (sign changes %d)" % found))
    # Part 2
    print("\nPart 2. Mittag-Leffler density (Mellin inversion with alpha_- = 1, E xi^s = "
          "Gamma(1+s)/Gamma(1+a s)); f(0) = 1/Gamma(1-a), f'(0) = -1/Gamma(1-2a)")
    for a in (0.3, 0.45, 0.5, 0.55, 0.6, 0.7, 0.8, 0.9, 0.95):
        h, dh = h_and_dh(W, a, 1.0)
        imax = int(np.argmax(h))
        print("  a=%.2f  f'(0) = %s  sign changes of f' on (1e-4, 1e4) = %d  argmax f = %.4g"
              % (a, ("%.4f" % (-1 / G(1 - 2 * a))) if abs(1 - 2 * a) > 1e-12 else "0",
                 sign_changes(dh), W[imax]))
    # Part 3
    from shape_engine import Engine, sibuya, zeta_law, modes
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    cases = [((0.75, 0.95), lambda n: (sibuya(0.75, n), sibuya(0.95, n))),
             ((0.3, 0.9), lambda n: (sibuya(0.3, n), sibuya(0.9, n))),
             ((0.7, 1.5), lambda n: (sibuya(0.7, n), zeta_law(1.5, n))),
             ((0.4, 1.5), lambda n: (sibuya(0.4, n), zeta_law(1.5, n)))]
    for (ap, am), mk in cases:
        lp, lm = mk(Nmax + 5)
        E = Engine(lp, lm, Nmax)
        if am < 1:
            _, dh = h_and_dh(W, ap, am)
            mh = 1 if sign_changes(dh) >= 2 else 0
            what = "h interior mode" if mh else "h decreasing"
        else:
            mh = 1 if ap > 0.5 else 0
            what = "Mittag-Leffler(%.2f) %s" % (ap, "has interior mode" if mh else "decreasing")
        r = am / ap
        # the critical-point equation of G is A x^2 + B x + C0 = 0
        A = (r - 1) * (am - ap + 1)
        B = (ap - 1) * (r - 2) + (am + 1) + (r - 1)
        C0 = ap - 1
        roots = [x.real for x in np.roots([A, B, C0]) if abs(x.imag) < 1e-12 and 0 < x.real < 1]
        xs = roots[0]
        Gx = lambda x: x ** (ap - 1) * (1 - x) ** (-am - 1) * ((1 - x) + r * x)
        print("\n== plus %s, minus %s: %s; bulk minimum of G at x* = %.4f (roots in (0,1): %d)"
              % (lp.name, lm.name, what, xs, len(roots)))
        for N in [n for n in (500, 1000, 2000, 3000, 4000) if n <= Nmax]:
            for st in (1, -1):
                P = E.fresh(N, st)
                mx, mn, gap = modes(P)
                print("  N=%5d start %+d modes=%d at %s; minima at %s; min rel gap %.1e"
                      % (N, st, len(mx), [a for a, b in mx], [a for a, b in mn], gap))
            P = E.fresh(N, 1)
            scale = math.sin(math.pi * ap) / math.pi * lm.T[N] / (N * lp.T[N])
            ratios = ["%.3f" % (P[int(x * N)] / (scale * Gx(x))) for x in (0.2, 0.4, 0.6, 0.8)]
            print("           P_N(xN) / (bulk formula) at x = 0.2, 0.4, 0.6, 0.8: %s" % ratios)
        del E
