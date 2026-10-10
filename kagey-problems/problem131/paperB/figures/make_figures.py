"""Figures for Paper B of Problem 131 (problem131_multistate.tex in the folder above).

Run from anywhere:  python -B make_figures.py

Each figure is sized for one column (3.37 in) or for the text width of the
papers (6.4 in on letter paper with 1.05 in margins; a journal full width
of 6.69 in also works), has no text smaller than 8 pt when included at its
natural size, and is written as vector PDF and 600 dpi PNG
next to this script. Colours go light to dark within a sweep and line styles
alternate, so the figures still read in greyscale.

  simplex   P_N(n)/V_N on the triangle (d = 3) below, at and above the crossing
  phases    the weak-field lines ell_k(t) for h_i = -(i-1)^2

The figures of Paper A are made by paperA/figures/make_figures.py, and the
program figure by figures/make_program_figure.py in the Problem 131 folder.

Small cases use exact rational arithmetic (fractions.Fraction). check()
compares every quoted number with the paper and stops if one disagrees.
"""

from __future__ import annotations

from fractions import Fraction
from math import log, pi, sqrt
from pathlib import Path

import logging

import matplotlib

matplotlib.use("Agg")
logging.getLogger("fontTools").setLevel(logging.ERROR)
import matplotlib.pyplot as plt
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


# The palette is batlow, from F. Crameri's Scientific colour maps (perceptually
# uniform, readable in grayscale and with color-vision deficiencies). Without
# the package cmcrameri the figures fall back to viridis.
try:
    from cmcrameri import cm as _cmc
    PALETTE = _cmc.batlow
except ImportError:
    PALETTE = plt.get_cmap("viridis")


def shades(n, cmap=None, lo=0.0, hi=0.82):
    """n colours from light to dark."""
    cm = PALETTE if cmap is None else plt.get_cmap(cmap)
    return [cm(x) for x in np.linspace(hi, lo, n)]


# ---------------------------------------------------------------- checks

def check():
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
    print("check: every quoted value agrees with the exact computation")


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
    cmap = PALETTE
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
        ax.plot(*xy(*c[:2]), "+", color="w", ms=6, mew=2.0)
        ax.plot(*xy(*c[:2]), "+", color="k", ms=5, mew=0.8)
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
    pc = fig_simplex()
    print(f"p_(24,3)^(3) = {pc:.8f}")
    print("tau_k for d = 5, h_i = -(i-1)^2:", [round(x, 4) for x in fig_phases()])
