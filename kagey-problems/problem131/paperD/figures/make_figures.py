"""Figures for Paper D of Problem 131 (endpoint crossings for random walks with memory).

Run from anywhere:
    python -B make_figures.py            use the cached data in ../data and compute what is missing
    python -B make_figures.py --rebuild  recompute every cache (about 15 minutes on 9 cores)

Each figure is 6.4 in wide (the text width of the paper, letter paper with
1.05 in margins), has no text smaller than 8 pt at its natural size, and is
written as vector PDF and 600 dpi PNG next to this script. Colours go light to
dark and line styles alternate, so the figures still read in greyscale.

  crossing  (no longer printed in the paper) x_n/log n for the elephant walk against g_n, the second-order
            formula, 2 z_n - log(2 pi) from the Markov walk and the leading terms,
            and D(n) log n against c_*
  shape     (Figure 2) the law of A_N at the crossing N = 3200 relative to the end,
            the bulk x f_N(m) against the Landau density, and the tail over x/(2 m^2)
  heavy     (Figure 3) R_N/(C(alpha) N^e(alpha)) for the stationary start, and R_N
            just below the golden ratio with the crossover sizes N*(alpha)
  (The paper writes N for the number of steps; the code below keeps n.)
Figure 1 of the paper is the program figure problem131/figures/program_D.pdf,
included directly as ../figures/program_D and made by
problem131/figures/make_program_figure.py, not here.

The data come from exact recursions in floating point and are cached in
../data/figdata_crossing.json, figdata_shape.json and figdata_heavy.json.
  Elephant walk. The minority count M_t never decreases. So P(A_n = n/2) needs only
      the states that can still reach n/2 (a forward window recursion), and the law of
      M_n on {0, ..., Mmax} is exact when the chain is cut at Mmax. The crossing x_n is
      the root of log C_n - log E_n with E_n = (1 - x/n)^(n-1)/2. At n = 10^6 the plots
      use x = 22.4407, the root g_n of x + log x = 2 log n - log 8, which is within
      10^-3 of the crossing by the second-order formula (the crossing itself was not
      computed at that size).
  Markov walk. The run-count formula for the center, as in Paper A.
  Landau density. f_L(l) = (1/pi) int_0^inf exp(-t log t - l t) sin(pi t) dt at 30 digits.
  Heavy tails. The two-renewal formula (Proposition 4.2) with FFT convolutions gives
      C_n for every even n up to 10^5 at once. The stationary end is zeta(alpha, n)/(2 zeta(alpha)).
check() tests the engines against brute force on small cases, then compares every
number that the paper quotes about the plotted data with the computed value, and
stops with a list of disagreements.
"""

from __future__ import annotations

import json
import logging
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from itertools import product
from math import exp, log, log1p, pi
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
logging.getLogger("fontTools").setLevel(logging.ERROR)
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
from scipy import fft as sfft
from scipy.optimize import brentq
from scipy.special import gammaln, logsumexp

HERE = Path(__file__).resolve().parent
DATA = HERE.parent / "data"
COL, FULL = 3.37, 6.4
PHI = (1 + 5 ** 0.5) / 2
EULER = 0.57721566490153286
C_STAR = 0.5 * log(2 * pi) - 0.25

plt.rcParams.update({
    "font.size": 8, "axes.labelsize": 8, "legend.fontsize": 8,
    "xtick.labelsize": 8, "ytick.labelsize": 8,
    "font.family": "serif", "mathtext.fontset": "cm",
    "axes.linewidth": 0.6, "lines.linewidth": 1.0,
    "xtick.direction": "in", "ytick.direction": "in",
    "xtick.top": True, "ytick.right": True,
    "savefig.bbox": "tight", "savefig.pad_inches": 0.02,
    "pdf.fonttype": 42,
})


def save(fig, name):
    fig.savefig(HERE / f"{name}.pdf")
    fig.savefig(HERE / f"{name}.png", dpi=600)
    plt.close(fig)
    print(f"wrote {name}.pdf and {name}.png")


def shades(n, cmap="viridis", lo=0.0, hi=0.85):
    """n colours from light to dark."""
    return [plt.get_cmap(cmap)(x) for x in np.linspace(hi, lo, n)]


def panel(ax, letter, x=0.03, y=0.95):
    ax.text(x, y, f"({letter})", transform=ax.transAxes, va="top")


# ---------------------------------------------------------------- elephant walk

def center_window(n, eps):
    """C_n = P(M_n = n/2) for even n, by the forward recursion on the feasible window."""
    h = n // 2
    P = np.zeros(h + 2)
    P[0] = 1.0
    for t in range(1, n):
        lo = max(0, h - (n - t))          # below lo the chain cannot reach h any more
        hi = min(t - 1, h)                # M_t <= t - 1, and states above h are useless
        b = np.arange(lo, hi + 1, dtype=float)
        r = eps + (1.0 - 2.0 * eps) * b / t
        seg = P[lo:hi + 1].copy()
        P[lo:hi + 1] = seg * (1.0 - r)
        P[lo + 1:hi + 2] += seg * r
        if lo > 0:
            P[lo - 1] = 0.0
    return P[h]


def endpoint(n, eps):
    """E_n = P(A_n = n) = (1 - eps)^(n-1)/2."""
    return 0.5 * exp((n - 1) * log1p(-eps))


def erw_crossing(n):
    """x_n = n eps_n with C_n = E_n (n even)."""
    f = lambda x: log(center_window(n, x / n)) - log(endpoint(n, x / n))
    return brentq(f, 0.3, 5 * log(n), xtol=1e-12)


def erw_law(n, eps):
    """P(A_n = a), a = 0..n, fair first step (A_n = number of +1 steps)."""
    P = np.zeros(n + 1)
    P[0] = P[1] = 0.5
    for k in range(1, n):
        a = np.arange(k + 1)
        up = (1 - eps) * a / k + eps * (1 - a / k)
        new = np.zeros(n + 1)
        new[1:k + 2] += P[:k + 1] * up
        new[:k + 1] += P[:k + 1] * (1 - up)
        P = new
    return P


def minority_law(n, x, c0, mmax):
    """P(Y_n = m), m = 0..mmax, for Y_1 = c0 and P(Y_{k+1} = Y_k + 1) = eps + (1 - 2 eps) Y_k/k.

    With c0 = 0 this is f_n(m) = P_+(M_n = m). With c0 = 1 it is the law of the
    number of +1 steps given X_1 = +1, so its value at m is f_n(n - m). Cutting
    the state space at mmax is exact because the chain never decreases."""
    eps = x / n
    p = np.zeros(mmax + 1)
    p[c0] = 1.0
    a = np.arange(mmax + 1, dtype=float)
    for k in range(1, n):
        L = min(k + 1, mmax + 1)
        move = p[:L] * (eps + (1.0 - 2.0 * eps) * a[:L] / k)
        p[:L] -= move
        if L < mmax + 1:
            p[1:L + 1] += move
        else:
            p[1:L] += move[:-1]
    return p


def g_root(n):
    """g_n, the root of x + log x = 2 log n - log 8."""
    L = 2 * log(n) - log(8)
    return brentq(lambda x: x + log(x) - L, 1e-9, L + 5, xtol=1e-15)


def x_second(n):
    """The second-order formula of Proposition 2.10 without its error term."""
    g = g_root(n)
    return g - (2 * g * log(n) + g * g / 2) / (n * (1 + 1 / g))


def x_leading(n):
    """2 log n - log log n - log 16, the leading terms of Theorem 2.7(b)."""
    return 2 * log(n) - log(log(n)) - log(16)


def markov_z(N):
    """z_N = N(1 - p_N) for the Markov walk of Paper A (N even), by the run-count formula.

    P(A_N = N/2)/P(A_N = N) = 2 sum_k W_k u^k with u = q/p, where W_k counts the
    words with N/2 letters of each kind, first letter +, and k switches."""
    h = N // 2
    lb = lambda a, b: gammaln(a + 1) - gammaln(b + 1) - gammaln(a - b + 1)
    r = np.arange(1, h + 1, dtype=float)
    k = np.concatenate([2 * r - 1, 2 * r[1:] - 2])
    lw = np.concatenate([2 * lb(h - 1, r - 1), lb(h - 1, r[1:] - 1) + lb(h - 1, r[1:] - 2)])
    lu = brentq(lambda s: log(2.0) + logsumexp(lw + k * s), -60.0, 5.0, xtol=1e-15)
    u = exp(lu)
    return N * u / (1 + u)


def landau(lam, dps=30):
    """The Landau density with int e^{-u l} f_L(l) dl = u^u."""
    with mp.workdps(dps):
        l = mp.mpf(lam)
        v = mp.quad(lambda t: mp.exp(-t * mp.log(t) - l * t) * mp.sin(mp.pi * t), [0, 1, 5, 20, 60])
        return float(v / mp.pi)


def landau_mode(dps=30):
    with mp.workdps(dps):
        d = lambda l: mp.quad(lambda t: -t * mp.exp(-t * mp.log(t) - l * t) * mp.sin(mp.pi * t),
                              [0, 1, 5, 20, 60])
        return float(mp.findroot(d, mp.mpf("-0.22")))


# ---------------------------------------------------------------- heavy-tailed runs

HEAVY_A = ["1.3", "1.5", "phi", "5/3", "1.7", "1.9"]      # panel (a) and Table 2
HEAVY_B = ["1.5", "1.55", "1.58", "1.59"]                 # panel (b) and Remark 4.6
ALPHA_TEX = {"phi": r"\varphi", "5/3": "5/3"}


def alpha_float(a):
    return {"phi": PHI, "5/3": 5 / 3}.get(a, None) or float(a)


def alpha_mp(a):
    if a == "phi":
        return (1 + mp.sqrt(5)) / 2
    if a == "5/3":
        return mp.mpf(5) / 3
    return mp.mpf(a)


def heavy_consts(a):
    """e(alpha), C(alpha), C_fr(alpha) of Corollary 4.5, at 30 digits."""
    with mp.workdps(30):
        al = alpha_mp(a)
        mu = mp.zeta(al)
        K = mp.gamma(2 - al) / (al - 1)
        C = mp.pi * (K * abs(mp.cos(mp.pi * al / 2))) ** (1 / al) / (
            4 * (al - 1) * mp.gamma(1 + 1 / al) * mu ** (1 + 1 / al))
        return {"e": float(1 - al + 1 / al), "C": float(C), "Cfr": float(C * (al - 1) * mu)}


def run_kernels(alpha, n):
    """p_k = P(xi = k) and T(k) = P(xi >= k) = k^-alpha for k = 0..n."""
    k = np.arange(n + 1, dtype=float)
    T = np.zeros(n + 1)
    T[1:] = k[1:] ** (-alpha)
    p = np.zeros(n + 1)
    p[1:] = T[1:] * (-np.expm1(-alpha * np.log1p(1.0 / k[1:])))
    return p, T


def heavy_centers(alpha, hmax, tol=1e-14):
    """C_{2h}, h = 0..hmax, for the fresh and the stationary start (Proposition 4.2).

    fresh       C = sum_m u_m(h) [q_m(h) + q_{m+1}(h)]
    stationary  C = sum_m [u_m(h) qD_{m+1}(h) + q_m(h)^2/mu],  qD_{m+1} = T*T*u_{m-1}/mu,
    with u_m = p^{*m}, q_m = T*u_{m-1}. The sum stops when P(tau_m <= hmax) < tol."""
    p, T = run_kernels(alpha, hmax)
    mu = float(mp.zeta(alpha))
    L = hmax + 1
    nfft = sfft.next_fast_len(2 * L)
    Fp, FT = sfft.rfft(p, nfft), sfft.rfft(T, nfft)
    FTT = sfft.rfft(sfft.irfft(FT * FT, nfft)[:L], nfft)

    def convs(u):
        Fu = sfft.rfft(u, nfft)
        return (sfft.irfft(Fp * Fu, nfft)[:L], sfft.irfft(FT * Fu, nfft)[:L],
                sfft.irfft(FTT * Fu, nfft)[:L])

    u0 = np.zeros(L)
    u0[0] = 1.0
    Zf, Zs = np.zeros(L), np.zeros(L)
    u_m, q_m, qD_next = convs(u0)
    m = 1
    while True:
        u_next, q_next, qD_nn = convs(u_m)
        Zf += u_m * (q_m + q_next)
        Zs += u_m * qD_next / mu + q_m * q_m / mu
        if m >= hmax or u_m.sum() < tol:
            break
        u_m, q_m, qD_next = u_next, q_next, qD_nn
        m += 1
    return Zf, Zs, m


def heavy_job(args):
    """R_n = E_n/C_n for every even n in [10, 2 hmax], stationary and fresh start."""
    a, hmax = args
    alpha = alpha_float(a)
    Zf, Zs, m = heavy_centers(alpha, hmax)
    Ns = np.arange(10, 2 * hmax + 1, 2)
    with mp.workdps(30):
        al = mp.mpf(alpha)
        mu = mp.zeta(al)
        z = mp.zeta(al, 10)
        edge = []
        for N in Ns:
            if N > 10:                     # zeta(a, N) = zeta(a, N-2) - (N-2)^-a - (N-1)^-a
                z -= mp.mpf(int(N) - 2) ** (-al) + mp.mpf(int(N) - 1) ** (-al)
            edge.append(float(z / (2 * mu)))
        last = float(mp.zeta(al, int(Ns[-1])) / (2 * mu))
    assert abs(edge[-1] / last - 1) < 1e-12
    R = np.array(edge) / Zs[Ns // 2]
    Rf = 0.5 * Ns.astype(float) ** (-alpha) / Zf[Ns // 2]
    return a, Ns.tolist(), R.tolist(), Rf.tolist(), m


# ---------------------------------------------------------------- caches

N_SHAPE = 3200
N_BIG, X_BIG, M_BIG = 10 ** 6, 22.4407, 10 ** 4
GRID = [50 * 2 ** k for k in range(11)]                 # 50, 100, ..., 51200


def sig(v, d=12):
    return [float(f"{x:.{d}g}") for x in v]


def build_crossing(pool):
    xs = list(pool.map(erw_crossing, GRID[::-1]))[::-1]
    dense = sorted({int(2 * round(v / 2)) for v in np.geomspace(40, 64000, 140)})
    zd = list(pool.map(markov_z, dense))
    return {"grid": GRID, "x": xs, "z": [markov_z(n) for n in GRID], "dense_n": dense, "dense_z": zd}


def build_shape(pool):
    f0 = pool.submit(minority_law, N_BIG, X_BIG, 0, M_BIG)
    f1 = pool.submit(minority_law, N_BIG, X_BIG, 1, M_BIG)
    lam = [round(v, 4) for v in np.arange(-3.0, 9.0001, 0.04)]
    fl = pool.map(landau, lam, chunksize=16)
    n = N_SHAPE
    x = erw_crossing(n)
    P = erw_law(n, x / n)
    f = minority_law(n, x, 0, n // 2)
    h0, h1 = f0.result(), f1.result()
    law = 0.5 * (h0 + h1)                  # P(A_n = n - m) for m <= 10^4
    msub = sorted(set(range(0, 401)) | set(np.unique(np.round(np.geomspace(400, M_BIG, 300)).astype(int)).tolist()))
    return {
        "n3200": {"n": n, "x": x, "ratio": sig(P / P[-1]), "center": float(P[n // 2]), "end": float(P[-1]),
                  "f": sig(f[:301]), "f_center": float(f[n // 2])},
        "n1e6": {"n": N_BIG, "x": X_BIG, "m": msub, "f": sig(h0[msub]), "mirror": sig(h1[msub]),
                 "f_mode": int(np.argmax(h0)), "law_mode": int(np.argmax(law)),
                 "f_last": float(h0[M_BIG]), "mirror_last": float(h1[M_BIG])},
        "landau": {"lam": lam, "f": list(fl), "mode": landau_mode()},
    }


def build_heavy(pool):
    jobs = [(a, 50000) for a in HEAVY_A] + [(a, 15000) for a in HEAVY_B if a not in HEAVY_A]
    out = {"consts": {a: heavy_consts(a) for a in dict.fromkeys(HEAVY_A + HEAVY_B + ["1.6"])}, "A": {}, "B": {}}
    res = {a: (np.array(Ns), np.array(R), m) for a, Ns, R, _, m in pool.map(heavy_job, jobs)}
    sub = set(np.unique(2 * np.round(np.geomspace(100, 10 ** 5, 400) / 2)).astype(int).tolist())
    for a in HEAVY_A:
        Ns, R, m = res[a]
        keep = np.isin(Ns, sorted(sub | {1600, 10000, 100000}))
        i = int(np.argmax(R))
        d = np.diff(R)
        out["A"][a] = {"N": Ns[keep].tolist(), "R": sig(R[keep]), "m_stop": m,
                       "cells": {str(N): float(R[Ns == N][0]) for N in (150, 1600, 10000, 100000)},
                       "argmax_N": int(Ns[i]), "max_R": float(R[i]),
                       "falls_before_max": int(np.sum(d[:i] <= 0)), "rises_after_max": int(np.sum(d[i:] >= 0))}
    for a in HEAVY_B:
        Ns, R, m = res[a]
        w = Ns <= 30000
        Ns, R = Ns[w], R[w]
        s = np.sign(R - 1)
        changes = [int(Ns[i]) for i in range(1, len(s)) if s[i] != s[i - 1]]
        pick = (Ns <= 400) | np.isin(Ns, np.unique(2 * np.round(np.geomspace(400, 30000, 400) / 2)))
        pick |= np.isin(Ns, [c + d for c in changes for d in (-2, 0)])
        out["B"][a] = {"N": Ns[pick].tolist(), "R": sig(R[pick]), "sign_changes": changes,
                       "R_at": {str(c + d): float(R[Ns == c + d][0]) for c in changes for d in (-2, 0)}}
    return out


BUILDERS = {"crossing": build_crossing, "shape": build_shape, "heavy": build_heavy}


def load_data(rebuild=False):
    DATA.mkdir(exist_ok=True)
    data, todo = {}, []
    for name in BUILDERS:
        path = DATA / f"figdata_{name}.json"
        if path.exists() and not rebuild:
            data[name] = json.loads(path.read_text())
        else:
            todo.append(name)
    if todo:
        with ProcessPoolExecutor(max_workers=9) as pool:
            for name in todo:
                t = time.time()
                print(f"computing figdata_{name}.json ...", flush=True)
                data[name] = BUILDERS[name](pool)
                (DATA / f"figdata_{name}.json").write_text(json.dumps(data[name]))
                print(f"   done in {time.time() - t:.0f} s", flush=True)
    return data


# ---------------------------------------------------------------- checks

# Table 1 of the paper (TABLE2 keeps its earlier number): n -> (x_n, g_n, x_n - x_2nd, x_n/log n, D(n))
TABLE2 = {50: ("3.9404868665", "4.288636", "+0.3452", "1.007", "-0.02123"),
          400: ("7.6292168962", "7.843768", "+0.0621", "1.273", "-0.03319"),
          1600: ("10.2405649147", "10.340051", "+0.0179", "1.388", "+0.02921"),
          3200: ("11.5468344808", "11.610464", "+0.0097", "1.431", "+0.04786"),
          12800: ("14.1588452626", "14.182921", "+0.0028", "1.497", "+0.06416"),
          51200: ("16.7784677365", "16.786946", "+0.0008", "1.547", "+0.06522")}
# the other grid points, from the notes (D1, Section 4 and the Markov comparison)
NOTES_X = {100: "5.0958966738", 200: "6.3405901682", 800: "8.9334617102",
           6400: "12.8524830457", 25600: "15.4672095164"}
# text after Table 1 (x_n/log n at n = 51200 only, the others are research notes) and after Theorem 2.8
TEXT_RATIO = {3200: "1.43", 12800: "1.50", 51200: "1.55"}
TEXT_D = {3200: "+0.0479", 12800: "+0.0642", 51200: "+0.0652"}
TEXT_CSTAR = {3200: "0.083", 12800: "0.071", 51200: "0.062"}
# Table 2 of the paper (TABLE3 keeps its earlier number): alpha -> (e, C, C_fr, R_1600, [ratio], R_1e4, [ratio], R_1e5, [ratio])
TABLE3 = {"1.3": ("+0.469231", "0.422717", "0.498631", "17.7593", "1.3180", "38.7537", "1.2171", "106.149", "1.1317"),
          "1.5": ("+0.166667", "0.647971", "0.846371", "2.14409", "0.9675", "2.9528", "0.9818", "4.37642", "0.9914"),
          "phi": ("0", "0.776132", "1.073675", "0.661763", "0.8526", "0.697331", "0.8985", "0.727689", "0.9376"),
          "5/3": ("-0.066667", "0.835101", "1.182237", "0.411815", "0.8064", "0.389307", "0.8614", "0.352822", "0.9102"),
          "1.7": ("-0.111765", "0.880046", "1.265508", "0.298369", "0.7733", "0.262005", "0.8334", "0.215839", "0.8881"),
          "1.9": ("-0.373684", "1.438986", "2.266075", "0.0449706", "0.4923", "0.0256505", "0.5569", "0.0121612", "0.6242")}
NSTAR = {"1.5": 26, "1.55": 192, "1.58": 2596, "1.59": 14530}
NSTAR_160 = 372660          # from the research notes (no longer quoted in the paper), not computed here (grid plus bisection in the notes)


def agree(paper, got):
    """True if got rounds to the printed decimal string paper."""
    s = paper.replace("+", "")
    dec = len(s.split(".")[1]) if "." in s else 0
    return abs(got - float(s)) <= 0.5 * 10 ** -dec + 1e-12


def brute_erw(n, eps):
    """P(A_n = a) by summing over all 2^n sign sequences (exact, eps a Fraction)."""
    law = [Fraction(0)] * (n + 1)
    for signs in product((1, -1), repeat=n - 1):
        w, plus = Fraction(1, 2), 1                     # X_1 = +1, then mirror
        for t, s in enumerate(signs, start=1):
            up = (1 - eps) * Fraction(plus, t) + eps * Fraction(t - plus, t)
            w *= up if s == 1 else 1 - up
            plus += s == 1
        law[plus] += w
        law[n - plus] += w
    return law


def brute_heavy(alpha, N):
    """P(A_N = N/2) for alternating runs, stationary start, by listing the compositions of N."""
    mu = float(mp.zeta(alpha))
    p = lambda k: k ** -alpha - (k + 1) ** -alpha
    T = lambda k: k ** -alpha
    total = 0.0

    def go(parts, left):
        nonlocal total
        if left == 0:
            if len(parts) == 1:
                return
            w = T(parts[0]) / mu * T(parts[-1])                 # first run D, last run censored
            for k in parts[1:-1]:
                w *= p(k)
            plus = sum(parts[0::2])
            total += w * ((plus == N // 2) + (N - plus == N // 2)) / 2
            return
        for k in range(1, left + 1):
            go(parts + [k], left - k)
    go([], N)
    return total


def check(data):
    bad = []

    def cmp(label, paper, got):
        if not agree(paper, got):
            bad.append(f"{label}: paper {paper}, computed {got:.10g}")

    # engines against brute force
    eps = Fraction(1, 7)
    law = brute_erw(12, eps)
    assert sum(law) == 1
    fl = erw_law(12, float(eps))
    assert np.allclose(fl, [float(v) for v in law], rtol=1e-13, atol=0)
    assert abs(center_window(12, float(eps)) / float(law[6]) - 1) < 1e-13
    assert abs(endpoint(12, float(eps)) / float(law[12]) - 1) < 1e-13
    f0 = minority_law(12, 12 * float(eps), 0, 12)
    f1 = minority_law(12, 12 * float(eps), 1, 12)
    assert np.allclose(0.5 * (f0[:13] + f1[:13])[::-1], fl, rtol=1e-12, atol=0)
    for a in (1.5, PHI):
        Zf, Zs, _ = heavy_centers(a, 7)
        for N in (8, 12, 14):
            assert abs(Zs[N // 2] / brute_heavy(a, N) - 1) < 1e-12
    assert abs(markov_z(2) - 2 / 3) < 1e-12              # p_2 = 2/3, so z_2 = 2/3

    # Table 1 (and the crossing figure, no longer printed)
    c = data["crossing"]
    X = dict(zip(c["grid"], c["x"]))
    Z = dict(zip(c["grid"], c["z"]))
    D = {n: X[n] - (2 * Z[n] - log(2 * pi)) for n in X}
    for n, (xs, gs, d2, rs, ds) in TABLE2.items():
        cmp(f"Table 1 x_{n} (10 decimals of the notes, the paper prints 6)", xs, X[n])
        cmp(f"Table 1 g_{n}", gs, g_root(n))
        cmp(f"Table 1 x_{n} - x_2nd", d2, X[n] - x_second(n))
        cmp(f"Table 1 x_{n}/log n", rs, X[n] / log(n))
        cmp(f"notes D({n}) (Table 1 prints D(n) log n)", ds, D[n])
    for n, s in NOTES_X.items():
        cmp(f"notes x_{n}", s, X[n])
    for n in TEXT_RATIO:
        cmp(f"text or notes x_{n}/log n", TEXT_RATIO[n], X[n] / log(n))
        cmp(f"text D({n})", TEXT_D[n], D[n])
        cmp(f"text c_*/log {n}", TEXT_CSTAR[n], C_STAR / log(n))
    cmp("c_*", "0.668939", C_STAR)
    if not (all(D[n] < 0 for n in X if n <= 400) and all(D[n] > 0 for n in X if n >= 800)):
        bad.append("D(n) should be negative up to n = 400 and positive from n = 800")
    if not all(X[n] < g_root(n) for n in X):
        bad.append("x_n < g_n should hold on the whole grid")

    # Figure 2
    s = data["shape"]
    a3 = s["n3200"]
    n, x = a3["n"], a3["x"]
    r = np.array(a3["ratio"])
    cmp("x_3200 (Figure 2)", "11.546834", x)
    if abs(a3["center"] / a3["end"] - 1) > 1e-8:
        bad.append(f"C_n/E_n at n = 3200 is {a3['center'] / a3['end']}, not 1")
    if abs(a3["f_center"] / a3["center"] - 1) > 1e-10:
        bad.append("C_n should equal f_n(n/2) at n = 3200")
    ms = n - (n // 2 + int(np.argmax(r[n // 2:])))
    if ms != 25 or int(np.argmax(r[:n // 2])) != 25:
        bad.append(f"mode distance m* at n = 3200: paper 25, computed {ms}")
    cmp("R_1 at n = 3200", "5.8048", r[n - 1])
    e3 = x / n
    cmp("Theorem 3.5 lower bound at n = 3200", "5.7943", x / (2 * (1 - e3)))
    cmp("Theorem 3.5 upper bound at n = 3200", "5.8121", x * (1 + 1 / n) ** 2 / (2 - 3 * e3) + e3 / (1 - e3))
    sg = np.sign(np.diff(r))
    nch = int(np.sum(sg[1:] != sg[:-1]))
    if nch != 3 or np.any(sg == 0):
        bad.append(f"sign changes of the first difference at n = 3200: paper 3, computed {nch}")
    b = s["n1e6"]
    cmp("g_n at n = 10^6 (the x used there)", "22.4407", g_root(N_BIG))
    if abs(x_second(N_BIG) - X_BIG) > 1e-3:
        bad.append(f"x = {X_BIG} is not within 1e-3 of the second-order crossing {x_second(N_BIG):.6f}")
    cmp("2x at n = 10^6 (research notes, not printed)", "44.9", 2 * X_BIG)
    if b["f_mode"] != 64 or b["law_mode"] != 64:
        bad.append(f"mode at n = 10^6: research notes 64, computed {b['f_mode']} and {b['law_mode']}")
    m = M_BIG
    tail = 0.5 * (b["f_last"] + b["mirror_last"]) / (X_BIG / m ** 2)
    cmp("P(A_n = n - 10^4)/(x/m^2) at n = 10^6", "0.51889", tail)
    cmp("notes H2, exact f_n(m) m(m+1)/x at m = 10^4", "1.03777", b["f_last"] * m * (m + 1) / X_BIG)
    cmp("notes H2, formula at m = 10^4", "1.0372", 1 + X_BIG * (2 * log(m) + 2 * EULER - 3) / m)
    cmp("heuristic factor near m = 70 at n = 1600 (close to 2)", "2", 1 + 10.2405649147 * (2 * log(70) + 2 * EULER - 3) / 70)
    cmp("Landau mode lambda_0", "-0.2227829813", s["landau"]["mode"])

    # Figure 3 and Table 2
    h = data["heavy"]
    for a, row in TABLE3.items():
        k = h["consts"][a]
        A = h["A"][a]["cells"]
        cmp(f"Table 2 e({a})", row[0], k["e"])
        cmp(f"Table 2 C({a})", row[1], k["C"])
        cmp(f"Table 2 C_fr({a})", row[2], k["Cfr"])
        for j, N in enumerate((1600, 10000, 100000)):
            R = A[str(N)]
            cmp(f"Table 2 R_{N} at alpha = {a}", row[3 + 2 * j], R)
            cmp(f"Table 2 ratio at N = {N}, alpha = {a}", row[4 + 2 * j], R / (k["C"] * N ** k["e"]))
    kphi = h["consts"]["phi"]
    cmp("C(phi)", "0.7761317206", kphi["C"])
    cmp("1/C(phi)", "1.2884", 1 / kphi["C"])
    with mp.workdps(30):
        ph = (1 + mp.sqrt(5)) / 2
        closed = mp.pi * ph * (ph * mp.gamma(ph ** -2) * abs(mp.cos(mp.pi * ph / 2))) ** (1 / ph) / (
            4 * mp.gamma(ph) * mp.zeta(ph) ** ph)
    if abs(float(closed) / kphi["C"] - 1) > 1e-14:
        bad.append("closed form of C(phi) disagrees with the general formula")
    Rphi = h["A"]["phi"]["cells"]["100000"]
    cmp("R_1e5 at phi", "0.72769", Rphi)
    cmp("R_1e5/C(phi)", "0.938", Rphi / kphi["C"])
    if h["A"]["phi"]["falls_before_max"] or h["A"]["phi"]["argmax_N"] != 100000:
        bad.append("R_n at alpha = phi should increase on the computed range")
    # The research notes say (the paper no longer prints this) that R_n rises over even n from 12 to 150 (not from the start). R_n falls
    # from R_2 = 0.5618 to R_12 = 0.41448 and then rises, so the one fall in [10, 150] is 10 -> 12.
    t53 = h["A"]["5/3"]
    _, Zs, _ = heavy_centers(5 / 3, 10)
    with mp.workdps(30):
        a53 = mp.mpf(5) / 3
        small = [float(mp.zeta(a53, N) / (2 * mp.zeta(a53))) / Zs[N // 2] for N in range(2, 22, 2)]
    ds = np.diff(small)
    if not (np.all(ds[:5] < 0) and np.all(ds[5:] > 0)):
        bad.append("alpha = 5/3: R_n should fall for even n from 2 to 12 and rise after 12")
    if t53["argmax_N"] != 150 or t53["falls_before_max"] != 1 or t53["rises_after_max"]:
        bad.append(f"alpha = 5/3: paper has R_n rising for 12 <= n <= 150 and falling after, computed max at "
                   f"{t53['argmax_N']} with {t53['falls_before_max']} falls before, {t53['rises_after_max']} rises after")
    cmp("R_12 at alpha = 5/3 (the minimum before the rise, research notes, not printed)", "0.41448", small[5])
    cmp("R_150 at alpha = 5/3", "0.42419", t53["cells"]["150"])
    k53 = h["consts"]["5/3"]
    cmp("ratio at 1e5, alpha = 5/3 (Table 2)", "0.910", t53["cells"]["100000"] / (k53["C"] * 1e5 ** k53["e"]))
    cmp("C(5/3) in Remark 4.6", "0.8351", k53["C"])
    for a, ns in NSTAR.items():
        ch = h["B"][a]["sign_changes"]
        if ch != [ns]:
            bad.append(f"n*({a}): paper {ns} (one sign change), computed sign changes at {ch}")
    fac = [NSTAR[a] / h["consts"][a]["C"] ** (-1 / h["consts"][a]["e"]) for a in NSTAR]
    fac.append(NSTAR_160 / h["consts"]["1.6"]["C"] ** (-1 / h["consts"]["1.6"]["e"]))
    cmp("smallest factor n*/C^(-1/e) (research notes, not printed)", "1.9", min(fac))
    cmp("largest factor n*/C^(-1/e) (research notes, not printed)", "7.4", max(fac))

    if bad:
        raise SystemExit("disagreements with the paper:\n  " + "\n  ".join(bad))
    print("check: every quoted value agrees with the exact computation")


# ---------------------------------------------------------------- crossing figure (no longer printed)

def fig_crossing(c):
    grid = np.array(c["grid"])
    X = np.array(c["x"])
    Z = np.array(c["z"])
    nd = np.array(c["dense_n"], dtype=float)
    zd = np.array(c["dense_z"])
    ns = np.geomspace(40, 64000, 300)
    L = np.log(ns)
    g = np.array([g_root(v) for v in ns])
    x2 = np.array([x_second(v) for v in ns])
    lead = np.array([x_leading(v) for v in ns])
    cols = shades(4)

    fig, (a, b) = plt.subplots(1, 2, figsize=(FULL, 2.3))
    a.plot(ns, g / L, "--", color=cols[0], label=r"root $g_n$")
    a.plot(ns, x2 / L, ":", color=cols[1], lw=1.3, label="second order")
    a.plot(nd, (2 * zd - log(2 * pi)) / np.log(nd), "-.", color=cols[2], label=r"$2z_n-\log 2\pi$")
    a.plot(ns, lead / L, "-", color=cols[3], lw=0.8, label="leading terms")
    a.plot(grid, X / np.log(grid), "o", color="k", ms=3.2, label=r"exact $x_n$", zorder=3)
    a.set_xscale("log")
    a.set_xlim(40, 64000)
    a.set_ylim(0.88, 1.62)
    a.set_xlabel(r"$n$")
    a.set_ylabel(r"$x_n/\log n$")
    a.legend(frameon=False, loc="lower right", handlelength=2.2)
    panel(a, "a")

    D = X - (2 * Z - log(2 * pi))
    b.axhline(0.0, color="0.6", lw=0.6, ls=":")
    b.axhline(C_STAR, color="k", lw=0.7, ls="--")
    b.text(55, C_STAR + 0.03, r"$c_*=\frac{1}{2}\log 2\pi-\frac{1}{4}$", va="bottom")
    b.plot(grid, D * np.log(grid), "-", color="0.45", lw=0.8, zorder=2)
    b.plot(grid, D * np.log(grid), "o", color="k", ms=3.2, zorder=3)
    b.set_xscale("log")
    b.set_xlim(40, 64000)
    b.set_ylim(-0.45, 0.9)
    b.set_xlabel(r"$n$")
    b.set_ylabel(r"$D(n)\,\log n$")
    panel(b, "b", x=0.9, y=0.12)
    fig.subplots_adjust(left=0.075, right=0.985, wspace=0.26)
    save(fig, "crossing")


# ---------------------------------------------------------------- Figure 2 shape

def fig_shape(s):
    a3, b6, ld = s["n3200"], s["n1e6"], s["landau"]
    n, x = a3["n"], a3["x"]
    r = np.array(a3["ratio"])
    col_s, col_b = shades(2, hi=0.7)
    fig, (a, b, c) = plt.subplots(1, 3, figsize=(FULL, 2.2), gridspec_kw={"width_ratios": [1.08, 1, 1]})

    # (a) the law relative to the end, with an inset near a = n
    k = np.arange(n + 1)
    a.plot(k, r, "-", color="k", lw=0.9)
    a.plot([n // 2], [1.0], "o", ms=3.5, mfc="white", mec="k", mew=0.8, zorder=3)
    a.annotate(r"$C_N=E_N$", (n // 2, 1.0), xytext=(n // 2, 0.17), ha="center", va="bottom")
    a.set_yscale("log")
    a.set_xlim(-60, n + 60)
    a.set_ylim(0.1, 1e4)
    a.set_xticks([0, 1600, 3200])
    a.set_xlabel(r"bin $a$ ($N=3200$)")
    a.set_ylabel(r"$P_N(a)/E_N$")
    panel(a, "a", x=0.09)
    ins = a.inset_axes([0.36, 0.47, 0.38, 0.35])
    mm = np.arange(0, 61)
    ins.plot(mm, r[n - mm], "-", color="k", lw=0.8)
    ins.plot(mm[:3], r[n - mm[:3]], "o", color="k", ms=2.2)
    ms = n - (n // 2 + int(np.argmax(r[n // 2:])))
    ins.axvline(ms, color="0.5", lw=0.6, ls="--")
    ins.set_yscale("log")
    ins.set_xlim(-2, 60)
    ins.set_ylim(0.4, 5e3)
    ins.set_xticks([0, ms, 50])
    ins.set_yticks([1, 1e3])
    ins.minorticks_off()
    ins.tick_params(length=2, pad=1.5)
    ins.set_xlabel(r"$N-a$", labelpad=0.5)

    # (b) the bulk against the Landau density
    lam = np.array(ld["lam"])
    b.plot(lam, ld["f"], "-", color="k", lw=1.0, label=r"Landau $f_L$")
    m6 = np.array(b6["m"])
    f6 = np.array(b6["f"])
    x6 = b6["x"]
    l6 = (m6 - x6 * np.log(x6)) / x6
    w = l6 <= 9
    b.plot(l6[w], x6 * f6[w], "--", color=col_b, lw=1.1, label=r"$N=10^6$")
    f3 = np.array(a3["f"])
    m3 = np.arange(len(f3))
    l3 = (m3 - x * np.log(x)) / x
    b.plot(l3, x * f3, "-.", color=col_s, lw=1.1, label=r"$N=3200$")
    b.axvline(ld["mode"], color="0.6", lw=0.5, ls=":")
    b.set_xlim(-3, 9)
    b.set_ylim(0, 0.235)
    b.set_xlabel(r"$\lambda_m=(m-x\log x)/x$")
    b.set_ylabel(r"$x\,f_N(m)$")
    b.legend(frameon=False, loc="upper right", handlelength=1.8)
    panel(b, "b")

    # (c) the tail divided by x/(2 m^2)
    m = np.arange(1, n // 2 + 1)
    c.plot(m, r[n - m] * a3["end"] * 2 * m ** 2 / x, "-", color=col_s, lw=1.1)
    law6 = 0.5 * (f6 + np.array(b6["mirror"]))
    g = m6 >= 1
    c.plot(m6[g], law6[g] * 2 * m6[g] ** 2 / x6, "--", color=col_b, lw=1.1)
    for xx, nn, cc in ((x, n, col_s), (x6, b6["n"], col_b)):
        mh = np.geomspace(2 * xx * log(xx), min(nn / xx, 1e4), 100)
        c.plot(mh, 1 + xx * (2 * np.log(mh) + 2 * EULER - 3) / mh, ":", color=cc, lw=1.3)
    c.plot([], [], ":", color="0.3", lw=1.3, label="heuristic")
    c.text(40, 2.3, r"$N=3200$", ha="right", va="center")
    c.text(200, 2.72, r"$N=10^6$", ha="left", va="center")
    c.axhline(1.0, color="k", lw=0.6, ls="--")
    c.set_xscale("log")
    c.set_xlim(1, 1e4)
    c.set_ylim(0, 3.1)
    c.set_xlabel(r"distance $m$ from the end")
    c.set_ylabel(r"$P_N(N-m)\cdot 2m^2/x$")
    c.legend(frameon=False, loc="lower right", handlelength=1.6)
    panel(c, "c")
    fig.subplots_adjust(left=0.07, right=0.99, wspace=0.42)
    save(fig, "shape")


# ---------------------------------------------------------------- Figure 3 heavy tails

def fig_heavy(h):
    fig, (a, b) = plt.subplots(1, 2, figsize=(FULL, 2.3))
    cols = shades(len(HEAVY_A))
    for i, al in enumerate(HEAVY_A):
        d, k = h["A"][al], h["consts"][al]
        N = np.array(d["N"], dtype=float)
        ratio = np.array(d["R"]) / (k["C"] * N ** k["e"])
        tex = ALPHA_TEX.get(al, al)
        a.plot(N, ratio, "-" if i % 2 == 0 else "--", color=cols[i], lw=1.1, label=rf"$\alpha={tex}$")
        cells = np.array([1600, 10000, 100000], dtype=float)
        a.plot(cells, [d["cells"][str(int(v))] / (k["C"] * v ** k["e"]) for v in cells], "o",
               ms=2.6, color=cols[i], mec="k", mew=0.4, zorder=3, clip_on=False)
    a.axhline(1.0, color="k", lw=0.6, ls=":")
    a.set_xscale("log")
    a.set_xlim(100, 1e5)
    a.set_ylim(0.3, 1.75)
    a.set_xlabel(r"$N$")
    a.set_ylabel(r"$R_N\,/\,C(\alpha)\,N^{e(\alpha)}$")
    a.legend(frameon=False, loc="upper right", ncol=3, handlelength=1.8, columnspacing=0.9)
    panel(a, "a", x=0.9, y=0.1)

    cols = shades(len(HEAVY_B))
    for i, al in enumerate(HEAVY_B):
        d = h["B"][al]
        N = np.array(d["N"], dtype=float)
        ns = NSTAR[al]
        b.plot(N, d["R"], "-" if i % 2 == 0 else "--", color=cols[i], lw=1.1,
               label=rf"$\alpha={al}$, $N^*={ns}$")
        b.plot([ns], [1.0], "o", ms=3.4, mfc="white", mec="k", mew=0.8, zorder=3)
    b.axhline(1.0, color="k", lw=0.6, ls="--")
    b.set_xscale("log")
    b.set_yscale("log")
    b.set_xlim(10, 3e4)
    b.set_ylim(0.5, 5.2)
    b.set_yticks([0.5, 1, 2, 4])
    b.set_yticklabels(["0.5", "1", "2", "4"])
    b.minorticks_off()
    b.set_xlabel(r"$N$")
    b.set_ylabel(r"$R_N=E_N/C_N$")
    b.legend(frameon=False, loc="upper left", handlelength=1.6)
    panel(b, "b", x=0.9, y=0.1)
    fig.subplots_adjust(left=0.075, right=0.985, wspace=0.26)
    save(fig, "heavy")


if __name__ == "__main__":
    data = load_data(rebuild="--rebuild" in sys.argv)
    check(data)
    fig_crossing(data["crossing"])
    fig_shape(data["shape"])
    fig_heavy(data["heavy"])
