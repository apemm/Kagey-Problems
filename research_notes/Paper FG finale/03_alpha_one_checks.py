"""Checks of the predictions P2-P10 of 03_alpha_one.md against the exact law.

Run:  py -I 03_alpha_one_checks.py          (about 10 minutes)
      py -I 03_alpha_one_checks.py --quick  (N <= 4000)
Output goes to stdout and to 03_alpha_one_output.txt next to this script.
"""
import importlib.util
import math
import sys
import time
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import gamma as Gamma

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("eng", HERE / "03_alpha_one_engine.py")
eng = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(eng)

QUICK = "--quick" in sys.argv
NS = [1000, 2000, 4000] if QUICK else [1000, 2000, 4000, 8000]
OUT = []
EG = 0.5772156649015329
_trap = getattr(np, "trapezoid", None) or np.trapz


def log(s=""):
    print(s, flush=True)
    OUT.append(s)


# ---------------------------------------------------------------- Levy exponents

def psi(u, index):
    """Levy exponent of the limit of (S_m - m mu(a_m))/a_m, Levy measure index x^(-index-1) dx,
    compensated by x 1{x <= 1}; for index 1 the measure is x^-2 dx."""
    u = np.asarray(u, dtype=float)
    au = np.abs(u)
    if index == 1.0:
        with np.errstate(divide="ignore", invalid="ignore"):
            lg = np.where(au > 0, np.log(au), 0.0)
        return -np.pi * au / 2 - 1j * u * lg + 1j * (1 - EG) * u
    a = index
    c = Gamma(2 - a) / (a - 1)
    return c * au ** a * np.exp(-1j * np.pi * a / 2 * np.sign(u)) + 1j * u * a / (a - 1)


def psi_quad(u, index):
    """the same exponent by quadrature, for the self-check"""
    nu = lambda x: index * x ** (-index - 1)
    sg = 1.0 if u >= 0 else -1.0
    au = abs(u)
    re = quad(lambda x: (math.cos(au * x) - 1) * nu(x), 0, 1, limit=400)[0] +         quad(nu, 1, np.inf, weight="cos", wvar=au)[0] - 1.0
    im1 = quad(lambda x: (math.sin(au * x) - au * x) * nu(x), 0, 1, limit=400)[0]
    im2 = quad(nu, 1, np.inf, weight="sin", wvar=au)[0]
    re, im1, im2 = re, sg * im1, sg * im2
    return re + 1j * (im1 + im2)


def density_W(xs, s_plus, s_minus, idx_minus=1.0):
    """density of W = s_plus Z - s_minus Z' at the points xs (absolute units); Z of index 1,
    Z' of index idx_minus."""
    sig = s_plus + s_minus
    tau = np.linspace(0.0, 60.0, 60001)[1:]
    t = tau / sig
    ph = np.exp(psi(s_plus * t, 1.0) + psi(-s_minus * t, idx_minus))
    xs = np.atleast_1d(np.asarray(xs, dtype=float))
    out = np.empty(len(xs))
    for i0 in range(0, len(xs), 200):
        xx = xs[i0:i0 + 200]
        integrand = (ph[None, :] * np.exp(-1j * np.outer(xx, t))).real
        out[i0:i0 + 200] = _trap(np.concatenate([np.ones((len(xx), 1)), integrand], axis=1),
                                    np.concatenate([[0.0], t])) / np.pi
    return out


# ---------------------------------------------------------------- scales

def a_of(law, m):
    """a with m T(a) = 1 (T continuous in our laws)."""
    if m <= 1:
        return 1.0
    return brentq(lambda a: m * float(law.T(a)) - 1.0, 1.0, 1e12 * m, xtol=1e-10)


def scales(lp, lm, N, mu_p, mu_m):
    def s_of(m):
        ap, am = a_of(lp, m), a_of(lm, m)
        return m * (mu_p[min(int(ap), len(mu_p) - 1)] + mu_m[min(int(am), len(mu_m) - 1)]) - N
    m = brentq(s_of, 1.0, float(N), xtol=1e-9)
    ap, am = a_of(lp, m), a_of(lm, m)
    Mp, Mm = mu_p[min(int(ap), len(mu_p) - 1)], mu_m[min(int(am), len(mu_m) - 1)]
    p = Mp / (Mp + Mm)
    return dict(m=m, ap=ap, am=am, mup=Mp, mum=Mm, p=p, sp=(1 - p) * ap, sm=p * am,
                sigma=(1 - p) * ap + p * am)


def semi_asymptotic(lp, lm, N, sc, idx, ks):
    """keep the exact tails in the run-sum identity and replace A(k', j') by its limit
    h_W(k' - p n')/(mu_+ + mu_-) of Lemma 1 (parameters frozen at N)."""
    p, c = sc["p"], sc["p"] * N
    grid = np.arange(-3 * N, 3 * N + 1, 4, dtype=float)
    hg = density_W(grid, sc["sp"], sc["sm"], idx)
    h = lambda x: np.interp(x, grid, hg, left=0.0, right=0.0)
    y = np.arange(1, N + 1, dtype=float)
    Tp, Tm = lp.T(y), lm.T(y)
    out = np.empty(len(ks))
    for i, k in enumerate(ks):
        x0 = k - c
        out[i] = np.dot(Tp[:k], h(x0 - (1 - p) * y[:k])) + np.dot(Tm[:N - k], h(x0 + p * y[:N - k]))
    return out / (sc["mup"] + sc["mum"])


def halfwidth(P, c):
    """half-width at half maximum around the maximum, by linear interpolation, both sides"""
    k0 = int(np.argmax(P))
    h = P[k0] / 2
    r = k0
    while P[r] > h:
        r += 1
    xr = r - 1 + (P[r - 1] - h) / (P[r - 1] - P[r])
    l = k0
    while P[l] > h:
        l -= 1
    xl = l + 1 - (P[l + 1] - h) / (P[l + 1] - P[l])
    return k0, xl, xr


def lamperti(x, a, b=1.0):
    return (math.sin(math.pi * a) / math.pi) * b * x ** (a - 1) * (1 - x) ** (a - 1) / (
        b * b * x ** (2 * a) + 2 * b * math.cos(math.pi * a) * x ** a * (1 - x) ** a + (1 - x) ** (2 * a))


# ---------------------------------------------------------------- main

def main():
    t0 = time.time()
    log("03_alpha_one_checks.py, N in %s" % NS)
    log()
    log("Self-check of the Levy exponents against quadrature:")
    for idx in (1.0, 1.5):
        for u in (0.3, 1.0, 2.5, -1.7):
            a, b = complex(psi(u, idx)), psi_quad(u, idx)
            log("  index %.1f u=%5.2f  closed %.10f%+.10fi  quad %.10f%+.10fi" % (idx, u, a.real, a.imag,
                                                                                b.real, b.imag))
    Q1, Q2, Q3 = eng.law_Q1(), eng.law_Q2(), eng.law_Q3()
    H, K = eng.law_power(0.5), eng.law_power(1.5)
    NMAX = max(NS)
    mu = {L.name: eng.truncated_mean(L, 4 * NMAX) for L in (Q1, Q2, Q3, H, K)}

    # Erickson's strong renewal theorem at alpha = 1 (input, checked): u(j) mu(j) -> 1
    log()
    log("Input check (Erickson): u(j) mu(j) for Q1 and Q2 (should tend to 1, slowly)")
    for L in (Q1, Q2):
        u, _ = eng.renewal(L, NMAX)
        log("  %-26s " % L.name + "  ".join("j=%d: %.4f" % (j, u[j] * mu[L.name][j])
                                             for j in (10, 100, 1000, NMAX)))

    laws = {}
    def get(lp, lm, N):
        key = (lp.name, lm.name, N)
        if key not in laws:
            laws[key] = eng.exact_law(lp, lm, N)
        return laws[key]

    # ---------------- P2, P3, P10: equal laws, fair start
    for L in (Q1, Q2):
        log()
        log("P2/P3 Cauchy bulk, %s both signs, fair start" % L.name)
        log("   N      m_N     gamma_N  gamma/N   R_N=pi*gamma*P(N/2)  HWHM/gamma  shape err(|x|<=3g_fit)")
        for N in NS:
            Pp, Pm = get(L, L, N)
            P = 0.5 * (Pp + Pm)
            sc = scales(L, L, N, mu[L.name], mu[L.name])
            g = (np.pi / 2) * sc["sigma"]
            R = np.pi * g * P[N // 2] if N % 2 == 0 else np.nan
            k0, xl, xr = halfwidth(P, N / 2)
            gf = (xr - xl) / 2
            ks = np.arange(N + 1)
            x = ks - N / 2
            sel = np.abs(x) <= 3 * gf
            err = np.abs(P[sel] / P[N // 2] - 1 / (1 + (x[sel] / gf) ** 2)).max()
            cau = 1 / (np.pi * g) / (1 + (x[sel] / g) ** 2)
            semi = semi_asymptotic(L, L, N, sc, 1.0, ks[sel])
            semi = 0.5 * (semi + semi[::-1])
            log("  %5d  %8.2f  %8.2f  %.4f   %.4f               %.4f      %.4f      max err/peak: Cauchy %.4f"
                "  semi-asymptotic %.4f"
                % (N, sc["m"], g, g / N, R, gf / g, err, np.abs(P[sel] - cau).max() / cau.max(),
                   np.abs(P[sel] - semi).max() / cau.max()))
            if L is Q1 and N == NS[-1]:
                # P10: Lamperti with alpha_eff at scale a_N and at scale N
                aN = sc["ap"]
                eps_a = float(L.T(aN)) * aN / sc["mup"]
                eps_N = float(L.T(N)) * N / mu[L.name][N]
                sel2 = (ks > 0) & (ks < N) & (np.abs(x) <= 3 * gf)
                for nm, eps in (("a_N", eps_a), ("N", eps_N)):
                    lam = np.array([lamperti(k / N, 1 - eps) for k in ks[sel2]]) / N
                    log("  P10 Lamperti alpha_eff = 1 - L/mu at scale %-3s: alpha_eff=%.4f  "
                        "max|P - Lam/N|/P(N/2) = %.4f   width ratio (Lamperti HWHM / exact) = %.3f"
                        % (nm, 1 - eps, np.abs(P[sel2] - lam).max() / P[N // 2],
                           (np.pi * eps / 4 * N) / gf))
                cau = 1 / (np.pi * g) / (1 + (x[sel2] / g) ** 2)
                log("  P10 Cauchy with gamma_N:                          max|P - Cauchy|/P(N/2) = %.4f"
                    % (np.abs(P[sel2] - cau).max() / P[N // 2]))

    # ---------------- P4, P9: unequal, fresh plus, compare with h_N
    for (lp, lm, idx) in ((Q1, Q3, 1.0), (Q1, K, 1.5)):
        log()
        log("P4/P9 local law vs h_N, plus %s, minus %s, fresh plus start" % (lp.name, lm.name))
        log("   N      p_N     sigma_N   beta_N   max|sig P - h|/max h (|x|<=3)   same vs Cauchy fit"
            "   right/left tail ratio at 3 sigma")
        for N in NS:
            Pp, _ = get(lp, lm, N)
            sc = scales(lp, lm, N, mu[lp.name], mu[lm.name])
            sig, c = sc["sigma"], sc["p"] * N
            ks = np.arange(N + 1)
            x = (ks - c) / sig
            sel = np.abs(x) <= 3
            h = density_W(ks[sel] - c, sc["sp"], sc["sm"], idx) * sig
            err = np.abs(sig * Pp[sel] - h).max() / h.max()
            beta = (sc["sp"] - sc["sm"]) / sig
            # best symmetric Cauchy fit (location, scale by half-width)
            k0, xl, xr = halfwidth(Pp, c)
            gf = (xr - xl) / 2
            cau = 1 / (np.pi * gf) / (1 + ((ks[sel] - (xl + xr) / 2) / gf) ** 2)
            errc = np.abs(Pp[sel] - cau).max() / Pp[sel].max()
            kr, kl = int(round(c + 3 * sig)), int(round(c - 3 * sig))
            semi = semi_asymptotic(lp, lm, N, sc, idx, ks[sel]) * sig
            log("  %5d  %.4f  %8.2f  %+.4f   %.4f                          %.4f              %.3f"
                "     semi-asymptotic err %.4f"
                % (N, sc["p"], sig, beta, err, errc, Pp[kr] / Pp[kl] if kl >= 0 else np.nan,
                   np.abs(sig * Pp[sel] - semi).max() / h.max()))

    # ---------------- P5, P6, P7: Q1 both, fresh plus: end layer, big-jump kernel, antimode
    log()
    log("P5 end layer, Q1 both, fresh plus: P_N(N-j)/(T_+(N) u_-(j))")
    u, V = eng.renewal(Q1, NMAX)
    U = np.concatenate([[0.0], np.cumsum(u)[:-1]])
    for N in NS:
        Pp, _ = get(Q1, Q1, N)
        TN = float(Q1.T(N))
        log("  N=%5d  " % N + "  ".join("j=%d: %.5f" % (j, Pp[N - j] / (TN * u[j])) for j in (0, 1, 2, 5, 10, 30)))
    log()
    log("P6 big-jump kernel, Q1 both, fresh plus: P_N(k)/K_N(k), L = k - j, K = T(L)u(j) + f(L)[U(j) + mu(L)V(j)]")
    log("   and the bare infinite density T(N)/mu(N) l^-2 (l = L/N)")
    for N in NS:
        Pp, _ = get(Q1, Q1, N)
        row, row2 = [], []
        for lf in (0.1, 0.2, 0.4, 0.6, 0.8, 0.95):
            Lk = int(round(lf * N))
            j = (N - Lk) // 2
            k = N - j
            Lk = k - j
            Kk = float(Q1.T(Lk)) * u[j] + float(Q1.f(Lk)) * (U[j] + mu[Q1.name][Lk] * V[j])
            row.append("l=%.2f: %.3f" % (Lk / N, Pp[k] / Kk))
            row2.append("%.3f" % (Pp[k] / (float(Q1.T(N)) / mu[Q1.name][N] * (Lk / N) ** -2)))
        log("  N=%5d  " % N + "  ".join(row) + "    bare: " + " ".join(row2))
    log()
    log("P7 antimode, Q1 both, fresh plus: interior minimum N - j* between the bulk and the plus end")
    for N in NS:
        Pp, _ = get(Q1, Q1, N)
        sc = scales(Q1, Q1, N, mu[Q1.name], mu[Q1.name])
        g = (np.pi / 2) * sc["sigma"]
        lo = int(N / 2 + g)
        kstar = lo + int(np.argmin(Pp[lo:]))
        jstar = N - kstar
        pred = brentq(lambda j: j - N / (4 * (math.log(j + 1) + EG - 1 + 1 / (2 * (j + 1)))), 1, N)
        # refined: minimise the kernel prediction K_N(N-j) over j
        js = np.arange(1, N // 4)
        Kv = np.array([float(Q1.T(N - 2 * jj)) * u[jj] + float(Q1.f(N - 2 * jj)) *
                       (U[jj] + mu[Q1.name][N - 2 * jj] * V[jj]) for jj in js])
        jK = int(js[np.argmin(Kv)])
        log("  N=%5d  j*=%5d   predicted N/(4 mu(j*)) = %7.1f  ratio %.3f   argmin of K_N: %5d  ratio %.3f"
            "   T(j*) N / (4 mu(N)) = %.3f" % (N, jstar, pred, jstar / pred, jK, jstar / jK,
                                             float(Q1.T(jstar)) * N / (4 * mu[Q1.name][N])))

    # ---------------- P8: mixed, Q1 plus, H minus, fair start
    log()
    log("P8 mixed: plus Q1 (index 1), minus T=n^-1/2, fair start; D_N = mu_+(1/T_-(N))/T_-(N)")
    log("   N      D_N     E[A_N]/D_N (2/pi=0.6366)   max|D P - exp(-pi y^2/4)| on y in [0.2,1.5]"
        "   same with mu_+ at D_N")
    for N in NS:
        Pp, Pm = get(Q1, H, N)
        P = 0.5 * (Pp + Pm)
        TmN = float(H.T(N))
        D = mu[Q1.name][int(1 / TmN)] / TmN
        ks = np.arange(N + 1)
        y = ks / D
        sel = (y >= 0.2) & (y <= 1.5)
        err = np.abs(D * P[sel] - np.exp(-np.pi * y[sel] ** 2 / 4)).max()
        D2 = mu[Q1.name][int(D)] / TmN
        y2 = ks / D2
        sel2 = (y2 >= 0.2) & (y2 <= 1.5)
        err2 = np.abs(D2 * P[sel2] - np.exp(-np.pi * y2[sel2] ** 2 / 4)).max()
        # mixture: count Y/T_-(N) of half-normal law, plus sum of M runs ~ M mu_+(M) + M Z
        yg = np.arange(0.0025, 4.0, 0.005)
        zg = np.linspace(-40.0, 400.0, 44001)
        gz = density_W(zg, 1.0, 0.0)
        mix = np.zeros(len(ks))
        for yy in yg:
            M = yy / TmN
            mix += 0.005 * np.exp(-np.pi * yy ** 2 / 4) * np.interp((ks - M * mu[Q1.name][int(M)]) / M, zg, gz,
                                                                     left=0.0, right=0.0) / M
        err3 = np.abs(D * (P[sel] - mix[sel])).max()
        log("  %5d  %7.1f   %.4f                     %.4f                                    %.4f"
            "     mixture predictor: %.4f" % (N, D, (ks * P).sum() / D, err, err2, err3))

    # ---------------- extra: the largest N for Q1 only
    for N in ([] if QUICK else [16000, 32000]):
        log()
        log("Q1 both, fair start, N = %d (trend of P2)" % N)
        Pp, Pm = eng.exact_law(Q1, Q1, N)
        P = 0.5 * (Pp + Pm)
        sc = scales(Q1, Q1, N, mu[Q1.name], mu[Q1.name])
        g = (np.pi / 2) * sc["sigma"]
        k0, xl, xr = halfwidth(P, N / 2)
        log("  m_N=%.2f gamma_N=%.2f R_N=%.4f HWHM/gamma=%.4f" % (sc["m"], g, np.pi * g * P[N // 2],
                                                                   (xr - xl) / 2 / g))
        TN = float(Q1.T(N))
        log("  end layer: " + "  ".join("j=%d: %.5f" % (j, Pp[N - j] / (TN * u[j])) for j in (1, 5, 10)))

    log()
    log("total time %.0f s" % (time.time() - t0))
    (HERE / "03_alpha_one_output.txt").write_text("\n".join(OUT) + "\n", encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
