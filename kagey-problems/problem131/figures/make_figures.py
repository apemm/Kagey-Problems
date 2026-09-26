"""Figures for the two Problem 131 papers.

Run from anywhere:  python -B make_figures.py

Each figure is sized for one column (3.37 in) or for the text width of the
two papers (6.4 in on letter paper with 1.05 in margins; a journal full width
of 6.69 in also works), has no text smaller than 8 pt when included at its
natural size, and is written as vector PDF and 600 dpi PNG
next to this script. Colours go light to dark within a sweep and line styles
alternate, so the figures still read in greyscale.

Paper A (problem131.tex):
  row10     bin probabilities of row 10 (N = 9) at p = 1/3, 1/2, 2/3, 5/6
  crossing  N(1 - p_N)/log N against N, with the Bessel root and the expansions
  lattice   the rook paths and blocked walks for the word RRLRLL
  allbin    1 - p_{a,N-a} against a, with the leading law and the edge law
  window    the critical window R_{N,k}(u_N + t/N) against exp(t - 2y^2)
Paper B (problem131_multistate.tex):
  simplex   P_N(n)/V_N on the triangle (d = 3) below, at and above the crossing
  phases    the weak-field lines ell_k(t) for h_i = -(i-1)^2

Small cases use exact rational arithmetic (fractions.Fraction). The crossings
for large N are roots of polynomials with positive coefficients, found by
bisection in floating point and compared with mpmath at 40 digits where the
paper quotes a value. check() compares every quoted number with the paper and
stops if one disagrees.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import comb, factorial, log, pi, sqrt
from pathlib import Path

import logging

import matplotlib

matplotlib.use("Agg")
logging.getLogger("fontTools").setLevel(logging.ERROR)
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np
from matplotlib.collections import PolyCollection
from matplotlib.tri import Triangulation

HERE = Path(__file__).resolve().parent
np.seterr(over="ignore", invalid="ignore")   # bisection overshoots are mapped to +inf below
COL, FULL = 3.37, 6.4

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


# ---------------------------------------------------------------- exact law

def run_count(a, b):
    """W(N,k,j) of Theorem 2.1 for a letters R and b letters L, as a list in j."""
    n = a + b
    if a == 0 or b == 0:
        return [1] + [0] * (n - 1)
    w = [0] * n
    for i in range(1, n):
        if 2 * i - 1 < n:
            w[2 * i - 1] += 2 * comb(a - 1, i - 1) * comb(b - 1, i - 1)
        if 2 * i < n:
            w[2 * i] += comb(a - 1, i) * comb(b - 1, i - 1) + comb(a - 1, i - 1) * comb(b - 1, i)
    return w


def pmf_exact(n, p):
    """P_N(k), k = 0..N, as Fractions (p a Fraction)."""
    q = 1 - p
    return [Fraction(1, 2) * sum(c * p ** (n - 1 - j) * q ** j for j, c in enumerate(run_count(k, n - k)))
            for k in range(n + 1)]


def pmf_dp(n, p):
    """The same law from the recursion of Proposition 2.2, as an independent check."""
    R = {1: Fraction(1, 2)}
    L = {0: Fraction(1, 2)}
    q = 1 - p
    for _ in range(n - 1):
        R, L = ({k + 1: p * R.get(k, 0) + q * L.get(k, 0) for k in range(n + 1)},
                {k: p * L.get(k, 0) + q * R.get(k, 0) for k in range(n + 1)})
    return [R.get(k, 0) + L.get(k, 0) for k in range(n + 1)]


def free_ratio(a, b, u, rmax=400):
    """S_{a,b}(u) = P_{a+b}(a)/P_{a+b}(0) (Section 6), for arrays a, b, u (float)."""
    a, b, u = (np.asarray(v, dtype=float) for v in np.broadcast_arrays(a, b, u))
    u2 = u * u
    term = np.ones_like(u)
    total = np.zeros_like(u)
    for r in range(rmax):
        total += term * (2 * u + (a + b - 2 - 2 * r) * u2 / (r + 1))
        term = term * np.maximum(a - 1 - r, 0) * np.maximum(b - 1 - r, 0) * u2 / (r + 1) ** 2
        if not term.any() or (r > 20 and np.all(term < 1e-18 * total)):
            break
    return np.where(np.isnan(total), np.inf, total)     # overflow only happens far above 1


def periodic_ratio(a, b, u, rmax=400):
    """R^P_{N,k}(u), the cyclic count of Section 7, for arrays a, b, u (float)."""
    a, b, u = (np.asarray(v, dtype=float) for v in np.broadcast_arrays(a, b, u))
    u2 = u * u
    term = u2.copy()                      # C(a-1,r-1) C(b-1,r-1) u^{2r} at r = 1
    total = np.zeros_like(u)
    for r in range(1, rmax):
        total += (a + b) / r * term
        term = term * np.maximum(a - r, 0) * np.maximum(b - r, 0) * u2 / r ** 2
        if not term.any() or (r > 20 and np.all(term < 1e-18 * total)):
            break
    return np.where(np.isnan(total), np.inf, total)


def root_increasing(f, lo, hi, iters=80):
    """Vectorized bisection for f(u) = 1 with f increasing in u."""
    lo = np.array(lo, dtype=float)
    hi = np.array(hi, dtype=float)
    for _ in range(iters):
        mid = (lo + hi) / 2
        above = f(mid) >= 1
        hi = np.where(above, mid, hi)
        lo = np.where(above, lo, mid)
    return (lo + hi) / 2


def central_u(ns):
    ns = np.asarray(ns)
    a, b = ns // 2, (ns + 1) // 2
    return root_increasing(lambda u: free_ratio(a, b, u), np.zeros(ns.shape), np.full(ns.shape, 0.5))


def central_u_mp(n, dps=40):
    """u_N at high precision, for comparison with Table 1."""
    with mp.workdps(dps):
        a, b = n // 2, (n + 1) // 2
        w = run_count(a, b)
        lo, hi = mp.mpf(0), mp.mpf("0.5")
        for _ in range(4 * dps):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if mp.polyval(w[::-1], mid) < 1 else (lo, mid)
        return (lo + hi) / 2


def bessel_series(x, nu, terms=200):
    """I_nu(2x) for nu = 0, 1 and an array x >= 0 (plain power series)."""
    x = np.asarray(x, dtype=float)
    term = x ** nu / factorial(nu) * np.ones_like(x)
    total = np.zeros_like(x)
    for r in range(terms):
        total += term
        term = term * x * x / ((r + 1) * (r + 1 + nu))
    return total


def bessel_root(h):
    """x_B with 2x(I_0(2x) + I_1(2x)) = h (Theorem 5.2)."""
    h = np.asarray(h, dtype=float)
    F = lambda x: 2 * x * (bessel_series(x, 0) + bessel_series(x, 1)) / h
    return root_increasing(F, np.zeros(h.shape), np.full(h.shape, 30.0))


# ---------------------------------------------------------------- checks

TABLE_PN = {2: "0.66666667", 3: "0.70710678", 4: "0.74487450", 5: "0.76759188",
            6: "0.78871211", 7: "0.80361731", 8: "0.81759938", 9: "0.82829163",
            10: "0.83840411", 11: "0.84652725", 12: "0.85426060", 20: "0.89293837",
            50: "0.94200405", 100: "0.96496633", 200: "0.97939018", 400: "0.98812464"}
RATIOS = {100: "0.9761", 200: "0.9864", 400: "0.9924",
          800: "0.99579", 1600: "0.99769", 3200: "0.99874"}


def check():
    notes = []
    # the exact law two ways, and row 10
    for p in (Fraction(1, 3), Fraction(1, 2), Fraction(2, 3), Fraction(5, 6)):
        assert pmf_exact(9, p) == pmf_dp(9, p)
        assert sum(pmf_exact(9, p)) == 1
    r = pmf_exact(9, Fraction(5, 6))
    assert r[4] < r[0], "at p = 5/6 the middle should be below the ends"
    # Table 1, rounded to 8 places
    for n, s in TABLE_PN.items():
        with mp.workdps(40):
            pn = 1 / (1 + central_u_mp(n))
            got = mp.nstr(pn, 8, strip_zeros=False)
        if abs(float(pn) - float(s)) > 5e-9:
            notes.append(f"Table 1, N={n}: paper {s}, computed {got}")
    pf = 1 / (1 + central_u(np.array(list(TABLE_PN))))
    assert np.allclose(pf, [float(s) for s in TABLE_PN.values()], atol=1e-8)
    with mp.workdps(40):
        assert abs(1 / (1 + central_u_mp(3)) - 1 / mp.sqrt(2)) < mp.mpf(10) ** -30
        p4 = 1 / (1 + central_u_mp(4))
        assert abs(3 * p4 ** 3 - 4 * p4 ** 2 + 4 * p4 - 2) < mp.mpf(10) ** -30
    # u_B/u_N quoted after Theorem 5.2
    for n, s in RATIOS.items():
        with mp.workdps(40):
            un = central_u_mp(n)
            h = mp.mpf(n) / 2
            xb = mp.findroot(lambda x: 2 * x * (mp.besseli(0, 2 * x) + mp.besseli(1, 2 * x)) - h, mp.log(n) / 2)
            ratio = xb / h / un
        digits = len(s) - 2
        if abs(float(ratio) - float(s)) > 0.5 * 10 ** -digits:
            notes.append(f"u_B/u_N at N={n}: paper {s}, computed {mp.nstr(ratio, 8)}")
    # the edge law: y_1 = 1, y_2 = sqrt 3 - 1
    assert abs(edge_y(1) - 1) < 1e-12 and abs(edge_y(2) - (sqrt(3) - 1)) < 1e-12
    # Paper B, Example 3.8 and the value of p_{k,k}
    u = Fraction(7, 20)
    assert 2 * u + 2 * u ** 2 + 2 * u ** 3 == Fraction(4123, 4000)
    assert 6 * u ** 2 + 6 * u ** 3 == Fraction(3969, 4000)
    P = simplex_law_exact(4, Fraction(10, 17))
    V = P[(4, 0, 0)]
    assert P[(2, 2, 0)] / V == Fraction(4123, 4000) and P[(2, 1, 1)] / V == Fraction(3969, 4000)
    for n in (3, 4, 6, 9):
        pc = simplex_crossing(n)
        if n == 3:
            assert abs(pc - 1 / (1 + 2 * 6 ** -0.5)) < 1e-12
        C, V = simplex_ratio_at(n, pc)
        assert abs(C / V - 1) < 1e-9
    # Paper B, cor:weakfield-full-hierarchy: t_k are the intersections of consecutive lines
    for d in (3, 4, 5, 6):
        for k in range(1, d):
            t = tau(k)
            assert abs(lam(k, t) - lam(k + 1, t)) < 1e-12
        assert all(tau(k) < tau(k + 1) for k in range(1, d - 1))
    if notes:
        raise SystemExit("disagreements with the paper:\n  " + "\n  ".join(notes))
    print("check: every quoted value agrees with the exact computation")


# ---------------------------------------------------------------- 1 row 10

def fig_row10():
    ps = [Fraction(1, 3), Fraction(1, 2), Fraction(2, 3), Fraction(5, 6)]
    cols = shades(4)
    k = np.arange(10)
    fig, axs = plt.subplots(1, 4, figsize=(FULL, 1.75), sharey=True)
    for ax, p, c, letter in zip(axs, ps, cols, "abcd"):
        P = pmf_exact(9, p)
        ax.bar(k, [float(v) for v in P], width=0.78, color=c, edgecolor="0.15", linewidth=0.4)
        ax.set_title(rf"$p={p.numerator}/{p.denominator}$", fontsize=8, pad=3)
        ax.set_xticks([0, 3, 6, 9])
        ax.set_xlim(-0.7, 9.7)
        ax.set_xlabel(r"bin $k$")
        ax.tick_params(top=False)
        if p == Fraction(5, 6):
            ax.axhline(float(P[0]), color="k", lw=0.6, ls="--")
            ax.annotate("ends", (0, float(P[0])), xytext=(1.2, 0.2),
                        arrowprops=dict(arrowstyle="-", lw=0.5, color="0.2"))
    axs[0].set_ylabel(r"$P_9(k)$")
    axs[0].set_ylim(0, 0.36)
    fig.subplots_adjust(left=0.075, right=0.995, wspace=0.08)
    save(fig, "row10")


# ---------------------------------------------------------------- 2 crossing

def fig_crossing():
    ns = np.arange(2, 10001)
    u = central_u(ns)
    exact = ns * u / (1 + u)                           # N(1 - p_N)
    h = ns / 2
    xb = bessel_root(h)
    ub = xb / h
    bessel = ns * ub / (1 + ub)
    L = np.log(ns)
    c0 = 0.5 * log(pi / 8)
    two = L - 0.5 * np.log(L) + c0
    three = two + (0.25 * np.log(L) - 0.5 * c0 + 0.125) / L

    # the values quoted in data/bessel_verification.txt
    for n, lead, ref in [(100, 0.12914282, -0.031648807), (400, 0.12120207, -0.013366348),
                         (3200, 0.10900593, -0.00011989957), (10000, 0.10144437, 0.0022341844)]:
        i = n - 2
        assert abs(exact[i] - two[i] - lead) < 1e-6 and abs(exact[i] - three[i] - ref) < 1e-6

    cols = shades(3)
    fig, (a, b) = plt.subplots(1, 2, figsize=(FULL, 2.3))
    m = ns >= 3
    a.axhline(1.0, color="0.6", lw=0.6, ls=":")
    a.plot(ns[m], two[m] / L[m], "-.", color=cols[0], label=r"$\nu_N$")
    a.plot(ns[m], three[m] / L[m], ":", color=cols[1], lw=1.2, label=r"$\nu_N$ + $1/L$ term")
    a.plot(ns, bessel / L, "--", color=cols[2], label="Bessel root $u_B$")
    a.plot(ns, exact / L, "-", color="k", lw=1.1, label="exact $z_N$")
    a.set_xscale("log")
    a.set_xlim(2, 1e4)
    a.set_ylim(0.45, 1.05)
    a.set_xlabel(r"$N$")
    a.set_ylabel(r"$z_N/\log N$")
    a.legend(frameon=False, loc="lower right", handlelength=2.2)
    panel(a, "a")

    b.axhline(0.0, color="0.6", lw=0.6, ls=":")
    b.plot(ns[m], (exact - two)[m], "-.", color=cols[0], label=r"minus $\nu_N$")
    b.plot(ns[m], (exact - three)[m], ":", color=cols[1], lw=1.2, label=r"minus $\nu_N$ + $1/L$ term")
    b.plot(ns, exact - bessel, "--", color=cols[2], label="minus Bessel root")
    b.set_xscale("log")
    b.set_xlim(2, 1e4)
    b.set_ylim(-0.1, 0.32)
    b.set_xlabel(r"$N$")
    b.set_ylabel(r"error in $z_N$")
    b.legend(frameon=False, loc="upper right", handlelength=2.2)
    panel(b, "b", y=0.12)
    fig.subplots_adjust(left=0.075, right=0.985, wspace=0.26)
    save(fig, "crossing")


# ---------------------------------------------------------------- 3 lattice

WORD = "RRLRLL"


def blocked(x, y):
    return (x % 3, y % 3) in ((1, 1), (2, 2))


def blocked_walks(a, b):
    """All walks (0,0) -> (3a,3b) with unit steps avoiding blocked points."""
    out = []

    def go(x, y, path):
        if (x, y) == (3 * a, 3 * b):
            out.append(path)
            return
        for dx, dy in ((1, 0), (0, 1)):
            nx, ny = x + dx, y + dy
            if nx <= 3 * a and ny <= 3 * b and not blocked(nx, ny):
                go(nx, ny, path + [(nx, ny)])
    go(0, 0, [(0, 0)])
    return out


def walk_word(path):
    """R for a right step landing on x = 0 mod 3, L for an up step landing on y = 0 mod 3."""
    w = ""
    for (x0, y0), (x1, y1) in zip(path, path[1:]):
        if x1 > x0 and x1 % 3 == 0:
            w += "R"
        if y1 > y0 and y1 % 3 == 0:
            w += "L"
    return w


def fig_lattice():
    a, b = WORD.count("R"), WORD.count("L")
    chg = sum(s != t for s, t in zip(WORD, WORD[1:]))
    rep = len(WORD) - 1 - chg
    # the two bijections, checked by brute force for this (a, b)
    walks = blocked_walks(a, b)
    groups = {}
    for w in walks:
        groups.setdefault(walk_word(w), []).append(w)
    assert all(len(g) == 2 ** sum(s != t for s, t in zip(k, k[1:])) for k, g in groups.items())
    n12 = pmf_exact(6, Fraction(1, 3))[a] * 2 * 3 ** 5
    assert len(walks) == n12, (len(walks), n12)
    mine = groups[WORD]
    assert len(mine) == 2 ** chg

    fig, (ax, bx) = plt.subplots(1, 2, figsize=(FULL, 3.0),
                                 gridspec_kw={"width_ratios": [1, 1]})
    # (a) rook path
    for i in range(a + 1):
        ax.plot([i, i], [0, b], color="0.85", lw=0.5, zorder=0)
    for j in range(b + 1):
        ax.plot([0, a], [j, j], color="0.85", lw=0.5, zorder=0)
    pts = [(0, 0)]
    for s in WORD:
        x, y = pts[-1]
        pts.append((x + 1, y) if s == "R" else (x, y + 1))
    xs, ys = zip(*pts)
    ax.plot(xs, ys, "-", color="k", lw=1.6, zorder=2, solid_capstyle="round")
    for i in range(1, len(WORD)):
        forced = WORD[i - 1] != WORD[i]
        ax.plot(*pts[i], "s", ms=6.5, zorder=3, mec="k", mew=0.9,
                mfc="k" if forced else "white")
    for e in (pts[0], pts[-1]):
        ax.plot(*e, "o", ms=5, color="k", zorder=3)
    # label the maximal runs
    runs, i = [], 0
    while i < len(WORD):
        j = i
        while j < len(WORD) and WORD[j] == WORD[i]:
            j += 1
        runs.append((WORD[i:j], pts[i], pts[j]))
        i = j
    for text, (x0, y0), (x1, y1) in runs:
        if y0 == y1:
            ax.text((x0 + x1) / 2, y0 - 0.13, text, ha="center", va="top")
        else:
            ax.text(x0 + 0.16, (y0 + y1) / 2, text, ha="left", va="center")
    ax.set_xlim(-0.35, a + 0.35)
    ax.set_ylim(-0.45, b + 0.35)
    ax.set_aspect("equal")
    ax.set_xticks(range(a + 1))
    ax.set_yticks(range(b + 1))
    ax.tick_params(top=False, right=False, length=0)
    for s in ax.spines.values():
        s.set_visible(False)
    ax.set_xlabel("R steps")
    ax.set_ylabel("L steps")
    ax.set_title(rf"$2^{{{rep}}}={2 ** rep}$ rook paths to $({a},{b})$ for {WORD}", fontsize=8)
    ax.plot([], [], "s", ms=6, mfc="k", mec="k", label="forced cut")
    ax.plot([], [], "s", ms=6, mfc="white", mec="k", label="optional cut")
    ax.legend(frameon=False, loc="upper left", bbox_to_anchor=(-0.02, 1.0), handletextpad=0.3)

    # (b) blocked walks
    n = 3
    for i in range(3 * a + 1):
        bx.plot([i, i], [0, 3 * b], color="0.9", lw=0.4, zorder=0)
    for j in range(3 * b + 1):
        bx.plot([0, 3 * a], [j, j], color="0.9", lw=0.4, zorder=0)
    bl = [(x, y) for x in range(3 * a + 1) for y in range(3 * b + 1) if blocked(x, y)]
    bx.plot(*zip(*bl), "x", ms=3.2, mew=0.7, color="0.55", zorder=1)
    corners = [(x, y) for x in range(0, 3 * a + 1, n) for y in range(0, 3 * b + 1, n)]
    bx.plot(*zip(*corners), "o", ms=2.4, color="0.55", zorder=1)
    edges = set()
    for w in mine:
        edges.update(zip(w, w[1:]))
    for (x0, y0), (x1, y1) in edges:
        bx.plot([x0, x1], [y0, y1], "-", color="k", lw=1.4, zorder=2, solid_capstyle="round")
    bx.set_xlim(-0.6, 3 * a + 0.6)
    bx.set_ylim(-0.6, 3 * b + 0.6)
    bx.set_aspect("equal")
    bx.set_xticks(range(0, 3 * a + 1, 3))
    bx.set_yticks(range(0, 3 * b + 1, 3))
    bx.tick_params(top=False, right=False, length=0)
    bx.set_xlabel(r"$x$")
    bx.set_ylabel(r"$y$")
    for s in bx.spines.values():
        s.set_visible(False)
    bx.set_title(rf"$2^{{{chg}}}={2 ** chg}$ blocked walks to $({3 * a},{3 * b})$ for {WORD}", fontsize=8)
    panel(ax, "a", x=-0.12, y=1.08)
    panel(bx, "b", x=-0.12, y=1.08)
    fig.subplots_adjust(left=0.06, right=0.995, wspace=0.18)
    save(fig, "lattice")


# ---------------------------------------------------------------- 4 all bins

def edge_y(a):
    """y_a with H_a(y_a) = 1 (the fixed-edge law of Section 6)."""
    coeffs = [comb(a - 1, r) / factorial(r + 1) for r in range(a)]      # of y^{r+1}
    H = lambda y: sum(c * y ** (r + 1) for r, c in enumerate(coeffs))
    lo, hi = 0.0, 1.0
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if H(mid) < 1 else (lo, mid)
    return (lo + hi) / 2


def fig_allbin():
    Ns = [100, 1000, 10000]
    cols = shades(3)
    styles = ["-", "--", "-"]
    fig, ax = plt.subplots(figsize=(COL, 2.6))
    for N, c, ls in zip(Ns, cols, styles):
        a = np.unique(np.round(np.geomspace(1, N // 2, 300)).astype(int))
        u = root_increasing(lambda v: free_ratio(a, N - a, v), np.zeros(a.shape), np.full(a.shape, 0.5))
        q = u / (1 + u)
        assert np.all(np.diff(q) < 0), "Proposition 6.1: 1 - p_{a,N-a} decreases toward the middle"
        if N == 100:          # the center is the table value p_100
            assert abs(1 - q[-1] - float(TABLE_PN[100])) < 1e-8
        ax.plot(a, q, ls, color=c, lw=1.1, label=rf"$N={N}$")
        g = a >= 2
        ax.plot(a[g], np.log(a[g]) / (2 * np.sqrt(a[g] * (N - a[g]))), ":", color=c, lw=1.0)
        e = np.arange(1, 7)
        ys = np.array([edge_y(k) for k in e])
        cs = np.sqrt(ys)
        bb = N - e
        ax.plot(e, cs / np.sqrt(bb) - (1 + cs ** 2) / bb, "o", ms=3.2, mfc="white", mec=c, mew=0.8)
    ax.plot([], [], ":", color="0.3", label=r"$\log a/(2\sqrt{ab})$")
    ax.plot([], [], "o", ms=3.2, mfc="white", mec="0.3", label="edge law")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlim(0.8, 6000)
    ax.set_ylim(5e-4, 0.25)
    ax.set_xlabel(r"distance $a$ from the edge ($b=N-a$)")
    ax.set_ylabel(r"$1-p_{a,N-a}$")
    ax.legend(frameon=False, loc="upper right", handlelength=2.0, ncol=1)
    save(fig, "allbin")


# ---------------------------------------------------------------- 5 window

def fig_window(N=10 ** 6):
    L = log(N)
    a0, b0 = N // 2, (N + 1) // 2
    top = 3 * L / N
    uF = float(root_increasing(lambda v: free_ratio(a0, b0, v), 0.0, top, 100))
    uP = float(root_increasing(lambda v: periodic_ratio(a0, b0, v), 0.0, top, 100))
    # the values recorded in data/periodic-window-verification.json at N = 10^6
    ref = {("free", -1): (0, "-0.043"), ("free", 1): (0.5, "0.0985"),
           ("periodic", 2): (1, "0.0033"), ("periodic", 1): (0.25, "0.0543")}
    ts = [-1, 0, 1, 2]
    cols = shades(4)
    ks = np.unique(np.round(N / 2 + np.linspace(-1.3, 1.3, 521) * N / sqrt(L)).astype(int))
    y = (ks - N / 2) * sqrt(L) / N
    yy = np.linspace(-1.3, 1.3, 400)
    fig, axs = plt.subplots(1, 2, figsize=(FULL, 2.4), sharey=True)
    for ax, name, law, uc, letter in [(axs[0], "free", free_ratio, uF, "a"),
                                      (axs[1], "periodic", periodic_ratio, uP, "b")]:
        for j, (t, c) in enumerate(zip(ts, cols)):
            u = uc + t / N
            R = law(ks, N - ks, u)
            ax.plot(y, R, "-", color=c, lw=1.2, label=rf"$t={t}$")
            ax.plot(yy, np.exp(t - 2 * yy ** 2), "--", color="k", lw=0.6)
            for (nm, tt), (y0, s) in ref.items():
                if nm == name and tt == t:
                    k0 = int(N / 2 + y0 * N / sqrt(L))
                    got = law(k0, N - k0, u) / np.exp(t - 2 * y0 ** 2) - 1
                    assert abs(got - float(s)) < 2e-3, (nm, tt, got, s)
        ax.axhline(1.0, color="0.6", lw=0.6, ls=":")
        ax.set_xlim(-1.3, 1.3)
        ax.set_ylim(0, 8.2)
        ax.set_xlabel(r"$y=(k-N/2)\sqrt{\log N}/N$")
        ax.set_title(f"{name} boundary", fontsize=8)
        panel(ax, letter)
    axs[0].set_ylabel(r"$R^X_{N,k}(u^X_N+t/N)$")
    axs[1].plot([], [], "--", color="k", lw=0.6, label=r"$e^{t-2y^2}$")
    axs[1].legend(frameon=False, loc="upper right", handlelength=1.8)
    fig.subplots_adjust(left=0.075, right=0.995, wspace=0.06)
    save(fig, "window")


# ---------------------------------------------------------------- 6 simplex (Paper B)

def simplex_law_exact(n, p):
    """P_N(n1, n2, n3) for d = 3, exact (p a Fraction), by the chain."""
    r = (1 - p) / 2
    cur = {((1, 0, 0), 0): Fraction(1, 3), ((0, 1, 0), 1): Fraction(1, 3), ((0, 0, 1), 2): Fraction(1, 3)}
    for _ in range(n - 1):
        nxt = {}
        for (cnt, s), w in cur.items():
            for t in range(3):
                c = list(cnt)
                c[t] += 1
                key = (tuple(c), t)
                nxt[key] = nxt.get(key, 0) + w * (p if t == s else r)
        cur = nxt
    out = {}
    for (cnt, _), w in cur.items():
        out[cnt] = out.get(cnt, 0) + w
    return out


def simplex_law(n, p):
    """The same in floating point, as an array P[i, j] with k = n - i - j."""
    r = (1 - p) / 2
    P = np.zeros((3, n + 1, n + 1, n + 1))
    P[0, 1, 0, 0] = P[1, 0, 1, 0] = P[2, 0, 0, 1] = 1 / 3
    for m in range(1, n):
        Q = np.zeros_like(P)
        for t in range(3):
            w = sum((p if s == t else r) * P[s] for s in range(3))
            if t == 0:
                Q[0, 1:] += w[:-1]
            elif t == 1:
                Q[1, :, 1:] += w[:, :-1]
            else:
                Q[2, :, :, 1:] += w[:, :, :-1]
        P = Q
    T = P.sum(axis=0)
    return np.array([[T[i, j, n - i - j] if i + j <= n else np.nan for j in range(n + 1)] for i in range(n + 1)])


def balanced(n, k):
    q, s = divmod(n, k)
    return (q + 1,) * s + (q,) * (k - s)


def simplex_ratio_at(n, p):
    P = simplex_law(n, p)
    c = balanced(n, 3)
    return P[c[0], c[1]], P[n, 0]


def simplex_crossing(n):
    lo, hi = 1 / 3, 1.0
    for _ in range(80):
        mid = (lo + hi) / 2
        C, V = simplex_ratio_at(n, mid)
        lo, hi = (mid, hi) if C > V else (lo, mid)
    return (lo + hi) / 2


def fig_simplex(n=24):
    pc = simplex_crossing(n)
    # the crossing from the exact rational law, bracketed at 6 decimals
    lo, hi = Fraction(round(pc * 10 ** 6) - 1, 10 ** 6), Fraction(round(pc * 10 ** 6) + 1, 10 ** 6)
    c = balanced(n, 3)
    for p, sign in ((lo, 1), (hi, -1)):
        E = simplex_law_exact(n, p)
        assert sign * (E[c] - E[(n, 0, 0)]) > 0
    ps = [0.78, pc, 0.88]
    labels = [r"$p=0.78$", rf"$p=p_{{{n},3}}^{{(3)}}\approx{pc:.4f}$", r"$p=0.88$"]
    s3 = sqrt(3) / 2

    def xy(i, j):             # barycentric (i, j, k)/n to the plane; vertex 1 at left
        k = n - i - j
        return (j + k / 2) / n, k * s3 / n

    hexr = 1 / (sqrt(3) * n) * 1.0
    ang = np.deg2rad(np.arange(6) * 60 + 30)
    hexv = np.c_[np.cos(ang), np.sin(ang)] * hexr
    vmin, vmax = -1, 1
    cmap = plt.get_cmap("viridis")
    fig, axs = plt.subplots(1, 3, figsize=(FULL, 2.0))
    for ax, p, lab, letter in zip(axs, ps, labels, "abc"):
        P = simplex_law(n, p)
        V = P[n, 0]
        pts, vals, polys = [], [], []
        for i in range(n + 1):
            for j in range(n + 1 - i):
                x, yv = xy(i, j)
                v = np.log10(P[i, j] / V)
                pts.append((x, yv))
                vals.append(v)
                polys.append(hexv + (x, yv))
        vals = np.array(vals)
        pc_ = PolyCollection(polys, array=np.clip(vals, vmin, vmax), cmap=cmap,
                             edgecolors="face", linewidths=0.2)
        pc_.set_clim(vmin, vmax)
        ax.add_collection(pc_)
        tri = Triangulation(*np.array(pts).T)
        ax.tricontour(tri, vals, levels=[0.0], colors="white", linewidths=1.0)
        ax.tricontour(tri, vals, levels=[0.0], colors="k", linewidths=0.4, linestyles="--")
        ax.plot(*xy(*c[:2]), "+", color="w", ms=5, mew=0.8)
        ax.set_xlim(-0.06, 1.06)
        ax.set_ylim(-0.08, s3 + 0.06)
        ax.set_aspect("equal")
        ax.axis("off")
        ax.set_title(lab, fontsize=8, pad=2)
        ax.text(0.0, s3 + 0.02, f"({letter})", va="bottom")
    cax = fig.add_axes([0.905, 0.14, 0.013, 0.68])
    cb = fig.colorbar(plt.cm.ScalarMappable(norm=plt.Normalize(vmin, vmax), cmap=cmap), cax=cax,
                      extend="both")
    cb.set_label(r"$\log_{10}\,P_N(n)/V_N$")
    cb.outline.set_linewidth(0.5)
    fig.subplots_adjust(left=0.0, right=0.885, bottom=0.0, top=0.92, wspace=0.03)
    save(fig, "simplex")
    return pc


# ---------------------------------------------------------------- 7 phases (Paper B)

H = 1.0


def c_k(k):
    return (k + 0.5) * log(k) - (k - 1) / 2 * log(4 * pi)


def lam(k, t):
    """ell_k(t) of eq:weakfield-lines in Paper B with h_i = -H (i-1)^2."""
    return (k - 1) * t + c_k(k) - H * (k - 1) * (2 * k - 1) / 6


def tau(k):
    return c_k(k) - c_k(k + 1) + H * (4 * k - 1) / 6


def fig_phases(d=5):
    taus = [tau(k) for k in range(1, d)]
    t = np.linspace(taus[0] - 1.2, taus[-1] + 1.2, 800)
    Lk = np.array([lam(k, t) for k in range(1, d + 1)])
    win = Lk.argmax(axis=0)
    for k in range(1, d + 1):                      # winners agree with the tau_k
        lo = taus[k - 2] if k > 1 else -np.inf
        hi = taus[k - 1] if k < d else np.inf
        inside = (t > lo + 1e-9) & (t < hi - 1e-9)
        assert np.all(win[inside] == k - 1)
    cols = shades(d)
    fig, ax = plt.subplots(figsize=(COL, 2.6))
    for i, k in enumerate(range(1, d + 1)):
        ax.plot(t, Lk[i], "-" if i % 2 == 0 else "--", color=cols[i], lw=0.8)
    env = Lk.max(axis=0)
    ax.plot(t, env, "-", color="k", lw=2.2, alpha=0.35, solid_capstyle="butt", zorder=0)
    ymin, ymax = env.min() - 2.2, env.max() + 0.6
    for i, tk in enumerate(taus):
        ax.axvline(tk, color="0.6", lw=0.5, ls=":")
    edges = [t[0]] + taus + [t[-1]]
    for k in range(1, d + 1):
        mid = (edges[k - 1] + edges[k]) / 2
        ax.text(mid, ymax - 0.15, str(k), ha="center", va="top")
    for i, k in enumerate(range(1, d + 1)):
        j = int(0.97 * len(t)) if k > 1 else int(0.03 * len(t))
        ax.text(t[-1] + 0.08, Lk[i][-1], rf"$\ell_{k}$", va="center", fontsize=8)
    ax.set_xlim(t[0], t[-1])
    ax.set_ylim(ymin, ymax)
    ax.set_xlabel(r"window parameter $t$")
    ax.set_ylabel(r"score $\ell_k(t)$")
    ax.text(t[0] + 0.05, ymax - 0.15, "size", ha="left", va="top", color="0.35")
    save(fig, "phases")
    return taus


if __name__ == "__main__":
    check()
    fig_row10()
    fig_crossing()
    fig_lattice()
    fig_allbin()
    fig_window()
    pc = fig_simplex()
    print(f"p_(24,3)^(3) = {pc:.8f}")
    print("tau_k for d = 5, h_i = -(i-1)^2:", [round(x, 4) for x in fig_phases()])
