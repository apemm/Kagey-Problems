"""Critical points of the Lamperti density L_{alpha,b}, 0 < alpha < 1, b > 0.

Run with `py -I`.  With t = log((1-x)/x), beta = log b, c = cos(pi alpha),
    L(x) proportional to phi(t) = (1 + cosh t) / (cosh(alpha t - beta) + c),
and the sign of phi'(t) is the sign of the exponential sum
    E(t) = (1-a)/2 sinh((1+a)t - beta) + (1+a)/2 sinh((1-a)t + beta)
           + c sinh t - a sinh(a t - beta),            a = alpha,
obtained from sinh t (cosh s + c) - a sinh s (1 + cosh t) with s = a t - beta.
We count sign changes of E on a fine grid in t (E has exponential growth at both ends) and
record the maximum count over a grid of (alpha, beta).  A zero of E is a critical point of
L, and its type follows from the sign change (x and t run in opposite directions).
"""
import math
import numpy as np


def E(t, a, beta):
    c = math.cos(math.pi * a)
    return ((1 - a) / 2 * np.sinh((1 + a) * t - beta) + (1 + a) / 2 * np.sinh((1 - a) * t + beta)
            + c * np.sinh(t) - a * np.sinh(a * t - beta))


def E_direct(t, a, beta):
    s = a * t - beta
    c = math.cos(math.pi * a)
    return np.sinh(t) * (np.cosh(s) + c) - a * np.sinh(s) * (1 + np.cosh(t))


def E_scaled(t, a, beta):
    """E(t) * exp(-(1+a)|t| - |beta|), computed without overflow."""
    c = math.cos(math.pi * a)
    M = (1 + a) * np.abs(t) + abs(beta)

    def sh(lam, gam):  # sinh(lam t + gam) * exp(-M)
        return 0.5 * (np.exp(lam * t + gam - M) - np.exp(-lam * t - gam - M))

    return ((1 - a) / 2 * sh(1 + a, -beta) + (1 + a) / 2 * sh(1 - a, beta)
            + c * sh(1.0, 0.0) - a * sh(a, -beta))


def zeros(a, beta, tmax=None, n=200001):
    if tmax is None:
        tmax = 30.0 + 3.0 * abs(beta) / max(a, 1e-2)
    t = np.linspace(-tmax, tmax, n)
    s = np.sign(E_scaled(t, a, beta))
    idx = np.where(s[1:] * s[:-1] < 0)[0]
    return t[idx]


def w_plus(a):
    c = math.cos(math.pi * a)
    return -c + a * math.sin(math.pi * a) / math.sqrt(1 - a * a)


def beta_c(a):
    """Half-width of the W window in beta = log b, for alpha > alpha_c.

    H(s) = 2a artanh(a R(s)) - s with R(s) = sinh s / (cosh s + cos(pi a)); the critical
    points of L_{a,b} are the solutions s of H(s) = log b.  H' > 0 iff cosh s < w_+(a).
    beta_c = H(s0), cosh s0 = w_+, if a R < 1 everywhere; infinite if a >= sin(pi a)."""
    c = math.cos(math.pi * a)
    if a >= math.sin(math.pi * a):
        return float("inf")
    w = w_plus(a)
    if w <= 1:
        return 0.0
    s0 = math.acosh(w)
    R = math.sinh(s0) / (w + c)
    return 2 * a * math.atanh(a * R) - s0


def predicted_count(a, beta):
    return 3 if abs(beta) < beta_c(a) else 1


if __name__ == "__main__":
    t = np.linspace(-5, 5, 11)
    for a in (0.3, 0.7):
        for beta in (0.0, 1.3):
            assert np.allclose(E(t, a, beta), E_direct(t, a, beta))
            M = (1 + a) * np.abs(t) + abs(beta)
            assert np.allclose(E_scaled(t, a, beta), E(t, a, beta) * np.exp(-M))
    print("exponential-sum identity checked")
    from scipy.optimize import brentq
    ac = brentq(lambda a: math.cos(math.pi * a / 2) - a, 0.1, 0.9)
    a1 = brentq(lambda a: a - math.sin(math.pi * a), 0.55, 0.95)
    print("alpha_c = %.12f (cos(pi a/2) = a),  alpha_1 = %.12f (a = sin(pi a))" % (ac, a1))
    for a in np.arange(0.02, 0.999, 0.02):
        for beta in np.arange(-6.0, 6.0001, 0.05):
            k = len(zeros(a, beta + 1e-7, n=60001))
            kp = predicted_count(a, beta + 1e-7)
            assert k == kp, (a, beta, k, kp)
    print("zero counts agree with the closed-form classification on the grid"
          " alpha = 0.02..0.98, |log b| <= 6")
    print("alpha   beta_c(alpha)   b_c = exp(beta_c)")
    for a in (0.6, 0.62, 0.65, 0.7, 0.72, 0.73, 0.735, 0.74, 0.8, 0.9):
        bc = beta_c(a)
        print("  %.3f  %s" % (a, ("%.6f   %.6f" % (bc, math.exp(bc))) if bc < 1e9 else "infinite"))
    # brute check of beta_c at alpha = 0.7: count just below and just above
    bc = beta_c(0.7)
    print("alpha = 0.7: count at beta_c - 1e-3:", len(zeros(0.7, bc - 1e-3)),
          " at beta_c + 1e-3:", len(zeros(0.7, bc + 1e-3)))
