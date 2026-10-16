"""Figures for Paper A of Problem 131 (problem131.tex in the folder above).

Run from anywhere:  python -B make_figures.py

Each figure is sized for one column (3.37 in) or for the text width of the
papers (6.4 in on letter paper with 1.05 in margins; a journal full width
of 6.69 in also works), has no text smaller than 8 pt when included at its
natural size, and is written as vector PDF and 600 dpi PNG
next to this script. Colours go light to dark within a sweep and line styles
alternate, so the figures still read in greyscale.

  row10     bin probabilities of row 10 (N = 9) below, at and above p_9
  crossing  N(1 - p_N)/log N against N, with the Bessel root and the expansions
  lattice   the rook paths and blocked walks for the word RRLRLL
  allbin    1 - p_{a,N-a} against a, with the leading law and the edge law, and the
            relative errors of the three approximations of the odds at N = 10^4
  window    the profile e^{-t} S^X_{N,k}(u^X_N + t/N) against e^{-2y^2}, and the count of bins
            above the endpoints against sqrt(2 max(t,0)), for N = 10^4, 10^6, 10^8
  layer     the boundary layer at odds v_N = N^{-kappa}, one row and the width against N

The plotted values are written to ../data/figures/fig_<name>.json, with the method and the
root tolerance. Run time is about two minutes.

The figures of Paper B are made by paperB/figures/make_figures.py, and the
program figure by figures/make_program_figure.py in the Problem 131 folder.
../../animations/animate.py imports pmf_exact and shades from this file.

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

HERE = Path(__file__).resolve().parent
np.seterr(over="ignore", invalid="ignore")   # bisection overshoots are mapped to +inf below
import sys as _sys
_sys.path.insert(0, str(HERE.parent.parent / "figures"))
import series_style as ss  # the shared style of the series (figures/series_style.py)

ss.use()
# Times text and STIX (Times-like) mathematics, as IOP recommends for figures
ss.plt.rcParams.update({"font.serif": ["Times New Roman", "STIXGeneral"], "mathtext.fontset": "stix"})
COL, FULL = ss.COL, ss.FULL
EXACT, PRIOR, PRIOR2, ACCENT, INK = (ss.SERIES[k] for k in ("exact", "prior", "prior2", "accent", "ink"))


def save(fig, name):
    out = HERE.parent / "tables_note" / "figures" if name == "lattice" else HERE
    fig.savefig(out / f"{name}.pdf")
    fig.savefig(out / f"{name}.png", dpi=600)
    plt.close(fig)
    print(f"wrote {name}.pdf and {name}.png")


def save_data(name, obj):
    """The plotted values, in paperA/data/figures/<name>.json."""
    import json
    out = HERE.parent / "data" / "figures"
    out.mkdir(parents=True, exist_ok=True)

    def conv(v):
        if isinstance(v, np.ndarray):
            return v.tolist()
        if isinstance(v, (np.floating, np.integer)):
            return v.item()
        raise TypeError(type(v))
    (out / f"{name}.json").write_text(json.dumps(obj, default=conv, indent=1) + "\n", encoding="utf-8")


def shades(n, cmap=None, lo=0.0, hi=1.0):
    """n colours along the gradient of the series (figures/series_style.py)."""
    return ss.shades(n, lo, hi)


def panel(ax, letter, x=0.03, y=0.95, ha="left", va="top"):
    ss.panel(ax, letter, x=x, y=y, ha=ha, va=va)


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
    """S_{a,b}(u) = P_{a+b}(a)/P_{a+b}(0) (Section 4), for arrays a, b, u (float)."""
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
    """S^P_{N,k}(u), the cyclic count of Section 5, for arrays a, b, u (float)."""
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
    if notes:
        raise SystemExit("disagreements with the paper:\n  " + "\n  ".join(notes))
    print("check: every quoted value agrees with the exact computation")


# ---------------------------------------------------------------- 1 row 10

def pmf_float(n, p):
    """P_N(k), k = 0..N, in floating point from the run counts of Theorem 2.1."""
    q = 1 - p
    return np.array([0.5 * sum(c * p ** (n - 1 - j) * q ** j for j, c in enumerate(run_count(k, n - k)))
                     for k in range(n + 1)])


def fig_row10():
    """Row ten (N = 9) below, at and above its crossing p_9, on a common vertical scale."""
    n = 9
    with mp.workdps(40):
        p9 = float(1 / (1 + central_u_mp(n)))
    ps = [(0.75, r"$p=3/4$, below $p_9$"), (p9, rf"$p=p_9={p9:.5f}$"), (0.9, r"$p=9/10$, above $p_9$")]
    cols = [ss.PURPLE, ACCENT, ss.GOLD]
    k = np.arange(n + 1)
    m = 2 * k - n                                         # the magnetization of bin k
    fig, axs = plt.subplots(1, 3, figsize=(FULL, 1.95), sharey=True)
    rows = []
    for ax, (p, title), c, letter in zip(axs, ps, cols, "abc"):
        P = pmf_float(n, p)
        assert abs(P.sum() - 1) < 1e-12
        rows.append({"p": p, "P": P})
        ax.bar(m, P, width=1.55, color=c, edgecolor=INK, linewidth=0.4)
        ax.axhline(P[0], color=INK, lw=0.7, ls=(0, (5, 3)))
        ax.set_title(title, fontsize=8, pad=3)
        ax.set_xticks([-9, -5, -1, 1, 5, 9])
        ax.set_xlim(-10.3, 10.3)
        ax.set_xlabel(r"magnetization $2k-9$")
        ax.tick_params(top=False)
        panel(ax, letter)
    # at p_9 the two central bins tie with the endpoints
    P9 = rows[1]["P"]
    assert abs(P9[4] - P9[0]) < 1e-12 and abs(P9[5] - P9[0]) < 1e-12
    assert rows[0]["P"][4] > rows[0]["P"][0] and rows[2]["P"][4] < rows[2]["P"][0]
    axs[0].set_ylabel(r"$P_9(k)$")
    axs[0].set_ylim(0, 0.27)
    fig.subplots_adjust(left=0.075, right=0.995, wspace=0.08)
    save(fig, "row10")
    save_data("fig_row10", {"N": n, "p_9": p9, "rows": rows,
                            "method": "run counts of Theorem 2.1 in double precision; p_9 by bisection "
                                      "of the run polynomial at 40 digits"})


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

    # one color per approximation, the same in both panels; only the Bessel root is dashed
    cols = [ss.GOLD, ss.PURPLE, INK]
    fig, (a, b) = plt.subplots(1, 2, figsize=(FULL, 2.3))
    m = ns >= 3
    a.axhline(1.0, color=ss.SERIES["grid"], lw=0.6)
    a.plot(ns[m], two[m] / L[m], "-", color=cols[0], lw=1.1, label=r"two-term $\nu_N$")
    a.plot(ns[m], three[m] / L[m], "-", color=cols[1], lw=1.1, label="three-term")
    a.plot(ns, bessel / L, "--", color=cols[2], lw=1.1, label="Bessel root $u_B$")
    a.plot(ns, exact / L, "-", color=EXACT, lw=1.6, label="exact $z_N$")
    a.set_xscale("log")
    a.set_xlim(2, 1e4)
    a.set_ylim(0.45, 1.05)
    a.set_xlabel(r"$N$")
    a.set_ylabel(r"$z_N/\log N$")
    a.legend(frameon=False, loc="lower right", handlelength=2.2)
    a.text(0.97, 0.87, "(a)", transform=a.transAxes, ha="right", va="top")   # clear of the line at 1

    b.axhline(0.0, color=ss.SERIES["grid"], lw=0.6)
    b.plot(ns[m], (exact - two)[m], "-", color=cols[0], lw=1.1, label=r"minus two-term")
    b.plot(ns[m], (exact - three)[m], "-", color=cols[1], lw=1.1, label="minus three-term")
    b.plot(ns, exact - bessel, "--", color=cols[2], lw=1.1, label="minus Bessel root")
    b.set_xscale("log")
    b.set_xlim(2, 1e4)
    b.set_ylim(-0.1, 0.32)
    b.set_xlabel(r"$N$")
    b.set_ylabel(r"error in $z_N$")
    b.legend(frameon=False, loc="upper right", handlelength=2.2)
    b.text(0.97, 0.04, "(b)", transform=b.transAxes, ha="right", va="bottom")   # clear of the curves
    fig.subplots_adjust(left=0.075, right=0.985, wspace=0.26)
    save(fig, "crossing")
    sel = np.unique(np.round(np.geomspace(2, 10000, 200)).astype(int)) - 2
    save_data("fig_crossing", {"N": ns[sel], "z_N": exact[sel], "bessel_root": bessel[sel],
                               "two_term": two[sel], "three_term": three[sel],
                               "method": "u_N by float bisection of the run polynomial "
                                         "(80 halvings of [0, 1/2]); x_B by bisection of the "
                                         "Bessel power series"})


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


def edge_gamma(a):
    """gamma_a of Theorem 4.8, from H_a' and H_a'' at y_a."""
    y = edge_y(a)
    c = [comb(a - 1, r) / factorial(r + 1) for r in range(a)]             # of y^{r+1}
    h1 = sum(cr * (r + 1) * y ** r for r, cr in enumerate(c))
    h2 = sum(cr * (r + 1) * r * y ** (r - 1) for r, cr in enumerate(c) if r >= 1)
    return (1 + y + (y + y * y / 2) * h2 / h1) / (2 * sqrt(y))


def uniform_odds(a, b):
    """The main terms of Theorem 4.7 for u_{a,b}, without the error term."""
    a, b = np.asarray(a, float), np.asarray(b, float)
    A = a * b / (a + b)
    eta = 2 * np.sqrt(a * b) / (a + b)
    ell = np.log(A)
    C = 0.5 * log(8 * pi) - np.log(1 + eta)
    B = (3 - eta) / (8 * (1 + eta))
    return (ell - 0.5 * np.log(ell) + C + (0.25 * np.log(ell) - 0.5 * C + B) / ell) / (2 * np.sqrt(a * b))


def fig_allbin():
    Ns = [100, 1000, 10000]
    cols = shades(3, hi=0.85)
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(FULL, 2.6))
    data = {"method": "u_{a,N-a} by float bisection of the run polynomial (80 halvings of [0, 1/2])"}
    for N, c in zip(Ns, cols):
        a = np.unique(np.round(np.geomspace(1, N // 2, 300)).astype(int))
        u = root_increasing(lambda v: free_ratio(a, N - a, v), np.zeros(a.shape), np.full(a.shape, 0.5))
        q = u / (1 + u)
        assert np.all(np.diff(q) < 0), "Proposition 4.1: 1 - p_{a,N-a} decreases toward the middle"
        if N == 100:          # the center is the table value p_100
            assert abs(1 - q[-1] - float(TABLE_PN[100])) < 1e-8
        ax.plot(a, q, "-", color=c, lw=1.2, label=rf"$N={N}$")
        g = a >= 2
        ax.plot(a[g], np.log(a[g]) / (2 * np.sqrt(a[g] * (N - a[g]))), ls=(0, (5, 3)), color=c, lw=0.9)
        e = np.arange(1, 7)
        ys = np.array([edge_y(k) for k in e])
        cs = np.sqrt(ys)
        bb = N - e
        ax.plot(e, cs / np.sqrt(bb) - (1 + cs ** 2) / bb, "o", ms=3.2, mfc="white", mec=c, mew=0.8)
        data[f"N={N}"] = {"a": a, "one_minus_p": q}
    ax.plot([], [], ls=(0, (5, 3)), color="0.3", lw=0.9, label=r"$\log a/(2\sqrt{ab})$")
    ax.plot([], [], "o", ms=3.2, mfc="white", mec="0.3", label="edge law")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlim(0.8, 6000)
    ax.set_ylim(5e-4, 0.25)
    ax.set_xlabel(r"distance $a$ from the edge ($b=N-a$)")
    ax.set_ylabel(r"switching probability $1-p_{a,N-a}$")
    ax.legend(frameon=False, loc="upper right", bbox_to_anchor=(1.0, 0.9), handlelength=2.2, ncol=1)
    panel(ax, "a", x=0.97, y=0.95)
    ax.texts[-1].set_ha("right")

    # (b) relative errors in the odds at N = 10^4
    N = 10 ** 4
    a = np.arange(1, N // 2 + 1)
    u = root_increasing(lambda v: free_ratio(a, N - a, v), np.zeros(a.shape), np.full(a.shape, 0.5), iters=90)
    b = N - a
    lead = np.log(a) / (2 * np.sqrt(a * b))
    unif = uniform_odds(a, b)
    ae = np.arange(1, 41)
    edge = np.array([sqrt(edge_y(k)) / sqrt(N - k) - 1 / (N - k) + edge_gamma(k) / (N - k) ** 1.5 for k in ae])
    gl, gu = a >= 2, a >= 4                         # log a > 0, and log log A defined
    err_lead = np.abs(lead[gl] / u[gl] - 1)
    err_unif = np.abs(unif[gu] / u[gu] - 1)
    err_edge = np.abs(edge / u[ae - 1] - 1)
    bx.plot(a[gl], err_lead, "-", color=ss.GOLD, lw=1.1, label=r"leading law $\log a/(2\sqrt{ab})$")
    bx.plot(a[gu], err_unif, "-", color=EXACT, lw=1.1, label="uniform expansion")
    bx.plot(ae, err_edge, "o", ms=3.0, color=ss.PURPLE, mfc=ss.PURPLE, mew=0, label="edge expansion")
    bx.set_xscale("log")
    bx.set_yscale("log")
    bx.set_xlim(0.8, 6000)
    bx.set_ylim(1e-7, 2)
    bx.set_xlabel(r"distance $a$ from the edge, $N=10^4$")
    bx.set_ylabel(r"relative error in the odds $u_{a,N-a}$")
    bx.legend(frameon=False, loc="lower right", bbox_to_anchor=(1.0, 0.0), handlelength=2.0)
    panel(bx, "b", x=0.97, y=0.95)
    bx.texts[-1].set_ha("right")
    fig.subplots_adjust(left=0.085, right=0.99, wspace=0.3)
    save(fig, "allbin")
    i100 = 99
    print(f"allbin (b): at a = 100 the errors are leading {err_lead[i100 - 1]:.3g}, "
          f"uniform {err_unif[i100 - 3]:.3g}; edge at a = 1, 6, 40: "
          f"{err_edge[0]:.2g}, {err_edge[5]:.2g}, {err_edge[39]:.2g}")
    data["errors_N=10000"] = {"a": a, "u": u, "leading": lead, "uniform": unif,
                              "edge_a": ae, "edge": edge}
    save_data("fig_allbin", data)


# ---------------------------------------------------------------- 5 window

def count_above(N, law, u):
    """M_N^X: the interior bins strictly above the endpoints, for an array of odds u.

    The interior ratios increase strictly toward the middle and are symmetric, so the bins above
    form an interval around the middle; its left end is found by bisection over k."""
    u = np.atleast_1d(np.asarray(u, float))
    m = N // 2
    smid = law(np.full(u.shape, m), np.full(u.shape, N - m), u)
    lo = np.ones(u.shape, dtype=np.int64)
    hi = np.full(u.shape, m, dtype=np.int64)
    for _ in range(64):
        mid = (lo + hi) // 2
        above = law(mid, N - mid, u) > 1
        hi = np.where(above, mid, hi)
        lo = np.where(above, lo, mid + 1)
    return np.where(smid > 1, N - 2 * lo + 1, 0)


def fig_window():
    """(a) the profile e^{-t} S^X at t = 1, (b) the count of bins above the endpoints."""
    Ns = [10 ** 4, 10 ** 6, 10 ** 8]
    cols = shades(3, hi=0.85)
    laws = [("free", free_ratio, "-"), ("periodic", periodic_ratio, (0, (5, 3)))]
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(FULL, 2.5))
    yy = np.linspace(-1.3, 1.3, 400)
    ts = np.linspace(-1, 4, 101)
    data = {"method": "central odds u_N^X by float bisection (200 halvings of [0, 3 log N/N]) of the "
                      "exact run polynomial (free) or cyclic run polynomial (periodic); ratios by the same "
                      "polynomials in double precision", "t_profile": 1.0}
    errs = {}
    for N, c in zip(Ns, cols):
        L = log(N)
        a0, b0 = N // 2, (N + 1) // 2
        ks = np.unique(np.round(N / 2 + np.linspace(-1.3, 1.3, 521) * N / sqrt(L)).astype(np.int64))
        y = (ks - N / 2) * sqrt(L) / N
        for name, law, ls in laws:
            uc = float(root_increasing(lambda v: law(a0, b0, v), 0.0, 3 * L / N, 200))
            prof = law(ks, N - ks, uc + 1.0 / N) / np.e
            ax.plot(y, prof, ls=ls, color=c, lw=1.1)
            M = count_above(N, law, uc + ts / N)
            bx.plot(ts, sqrt(L) * M / N, ls=ls, color=c, lw=1.1)
            errs[(N, name)] = float(law(a0, b0, uc + 2.0 / N) / np.exp(2.0) - 1)
            data[f"{name} N={N}"] = {"u_center": uc, "y": y, "profile_t1": prof, "t": ts, "M": M,
                                     "rel_err_t2_y0": errs[(N, name)]}
            if N == 10 ** 6:
                # the values recorded in data/periodic-window-verification.json at N = 10^6
                ref = {("free", -1): (0, "-0.043"), ("free", 1): (0.5, "0.0985"),
                       ("periodic", 2): (1, "0.0033"), ("periodic", 1): (0.25, "0.0543")}
                for (nm, tt), (y0, s) in ref.items():
                    if nm == name:
                        k0 = int(N / 2 + y0 * N / sqrt(L))
                        got = law(k0, N - k0, uc + tt / N) / np.exp(tt - 2 * y0 ** 2) - 1
                        assert abs(got - float(s)) < 2e-3, (nm, tt, got, s)
    ax.plot(yy, np.exp(-2 * yy ** 2), "-", color=INK, lw=0.7, zorder=0)
    ax.set_xlim(-1.3, 1.3)
    ax.set_ylim(0, 1.25)
    ax.set_xlabel(r"$y=(k-N/2)\sqrt{\log N}/N$")
    ax.set_ylabel(r"$e^{-t}S^X_{N,k}(u^X_N+t/N)$ at $t=1$")
    tt = np.linspace(-1, 4, 400)
    bx.plot(tt, np.sqrt(2 * np.maximum(tt, 0)), "-", color=INK, lw=0.7, zorder=0)
    bx.set_xlim(-1, 4)
    bx.set_ylim(0, 3.1)
    bx.set_xlabel(r"$t$")
    bx.set_ylabel(r"$\sqrt{\log N}\,M^X_N(t)/N$")
    for N, c in zip(Ns, cols):
        bx.plot([], [], "-", color=c, lw=1.1, label=rf"$N=10^{{{int(round(log(N, 10)))}}}$")
    bx.plot([], [], "-", color="0.35", lw=1.1, label="free")
    bx.plot([], [], ls=(0, (5, 3)), color="0.35", lw=1.1, label="periodic")
    bx.plot([], [], "-", color=INK, lw=0.7, label="limit")
    bx.legend(frameon=False, loc="upper left", handlelength=2.2)
    panel(ax, "a", x=0.97, y=0.95)
    ax.texts[-1].set_ha("right")
    panel(bx, "b", x=0.97, y=0.05, va="bottom")
    bx.texts[-1].set_ha("right")
    fig.subplots_adjust(left=0.075, right=0.99, wspace=0.27)
    save(fig, "window")
    for k, v in errs.items():
        print(f"window: relative error at t = 2, y = 0, {k}: {v:.4f}")
    save_data("fig_window", data)


# ---------------------------------------------------------------- Figure 4, boundary layer

def layer_width(N, v):
    """L_N = #{1 <= k <= N/2 : P_N(k) < P_N(0)} at odds v, by bisection (ratios increase inward)."""
    m = N // 2
    if free_ratio(m, N - m, v) < 1:
        return m
    lo, hi = 1, m
    while lo < hi:
        mid = (lo + hi) // 2
        if free_ratio(mid, N - mid, v) >= 1:
            hi = mid
        else:
            lo = mid + 1
    return lo - 1


def layer_refined(N, v):
    """The edge distance a at which the main terms of Theorem 4.7 equal v (real a, by bisection)."""
    f = lambda a: float(uniform_odds(a, N - a)) - v
    lo, hi = 4.0, N / 2
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if f(mid) > 0 else (lo, mid)
    return (lo + hi) / 2


def fig_layer():
    kappas = [0.6, 0.7, 0.8]
    cols = shades(3, hi=0.85)
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(FULL, 2.5))
    data = {"method": "ratios S_{k,N-k}(v) from the run polynomial in double precision; L_N by "
                      "bisection over k using the strict inward ordering of Proposition 4.1"}
    # (a) one row, N = 10^8 and v = N^{-0.7}
    N, kap = 10 ** 8, 0.7
    v = N ** (-kap)
    k = np.unique(np.round(np.geomspace(1, N // 2, 600)).astype(np.int64))
    logS = np.log(free_ratio(k, N - k, v))
    Lw = layer_width(N, v)
    ax.axvspan(1, Lw + 0.5, color=ss.SERIES["grid"], alpha=0.35, lw=0)
    ax.axhline(0, color=INK, lw=0.6)
    ax.plot(k, logS, "-", color=EXACT, lw=1.2)
    ax.axvline(Lw + 0.5, color=ACCENT, lw=0.8, ls=(0, (5, 3)))
    ax.set_xscale("log")
    ax.set_xlim(1, N / 2)
    ax.set_ylim(-10, 40)
    ax.set_xlabel(r"distance $k$ from the edge")
    ax.set_ylabel(r"$\log\,(P_N(k)/P_N(0))$")
    ax.text(1.6, 30, rf"$N=10^8$, $v_N=N^{{-0.7}}$" "\n" rf"$\mathcal{{L}}_N={Lw}$", va="top")
    panel(ax, "a", x=0.97, y=0.05, va="bottom")
    ax.texts[-1].set_ha("right")
    data["row"] = {"N": N, "kappa": kap, "k": k, "logS": logS, "L_N": Lw}
    # (b) the width against N
    es = np.arange(6, 12.01, 0.5)          # below 10^6 the hypotheses fail visibly for kappa = 0.8
    for kap, c in zip(kappas, cols):
        rl, rr, Ns = [], [], []
        for e in es:
            N = int(round(10 ** e))
            v = N ** (-kap)
            Lw = layer_width(N, v)
            Om = 1 / (sqrt(N) * v)
            rl.append(Lw / (Om ** 2 * log(Om) ** 2))
            rr.append(Lw / layer_refined(N, v))
            Ns.append(N)
        bx.plot(Ns, rl, "-", color=c, lw=1.1, marker="o", ms=2.6, label=rf"$\kappa={kap}$")
        data[f"kappa={kap}"] = {"N": Ns, "ratio_leading": rl, "ratio_refined": rr}
        print(f"layer: kappa = {kap}, L_N/(Omega^2 log^2 Omega) from {rl[0]:.3f} to {rl[-1]:.3f}, "
              f"L_N/a_refined from {rr[0]:.4f} to {rr[-1]:.4f}, max |.-1| {max(abs(r - 1) for r in rr):.4f}")
    bx.axhline(1, color=INK, lw=0.6)
    bx.set_xscale("log")
    bx.set_xlim(6e5, 1.6e12)
    bx.set_ylim(0, 4.5)
    bx.set_xlabel(r"$N$")
    bx.set_ylabel(r"$\mathcal{L}_N/(\Omega_N^2\log^2\Omega_N)$")
    bx.legend(frameon=False, loc="upper right", handlelength=2.2)
    panel(bx, "b", x=0.03, y=0.05, va="bottom")
    fig.subplots_adjust(left=0.075, right=0.99, wspace=0.27)
    save(fig, "layer")
    save_data("fig_layer", data)


if __name__ == "__main__":
    check()
    fig_row10()
    fig_crossing()
    # The lattice figure belongs to tables_note/, so it is saved there.
    fig_lattice()
    fig_allbin()
    fig_window()
    fig_layer()
