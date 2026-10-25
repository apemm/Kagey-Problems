"""Figure `aging`: the exact law of the counts of the fresh-or-repeat chain.

The law is the one of Proposition `prop:aging-urn`,
    P(M_T = m) = T!/(d theta)^(T) * prod_i theta^(m_i)/m_i!,
where x^(m) is the rising factorial. Panel (a) is two states, and panels (b)
and (c) are three states on the simplex, colored by the probability of a count vector
relative to the uniform law (which is the law at theta = 1). The interior of
the simplex, its edges and its corners are drawn apart.

Run:  python make_aging_figure.py     (a second)
"""
from math import lgamma, log, sqrt
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.collections import PolyCollection
from matplotlib.patches import Circle
from matplotlib.tri import Triangulation

HERE = Path(__file__).resolve().parent
FULL = 6.4
T2, T3 = 40, 36
THETAS = (0.5, 1.0, 2.0)

import sys as _sys
_sys.path.insert(0, str(HERE.parent.parent / "figures"))
import dark_style  # the manim palette, see figures/dark_style.py
dark_style.light()  # white background
PALETTE = dark_style.HEAT

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


def log_rising(x, m):
    return lgamma(x + m) - lgamma(x)


def log_law(m, theta):
    T, d = sum(m), len(m)
    r = lgamma(T + 1) - log_rising(d * theta, T)
    for mi in m:
        r += log_rising(theta, mi) - lgamma(mi + 1)
    return r


def xy(m):
    s = sum(m)
    return (m[2] + 0.5 * m[1]) / s, (sqrt(3) / 2) * m[1] / s


def figure():
    fig, axes = plt.subplots(1, 3, figsize=(FULL, 2.2), gridspec_kw={"width_ratios": [1.25, 1, 1]})
    cols = [dark_style.YELLOW, dark_style.BLUE, dark_style.RED]
    a = axes[0]
    k = np.arange(T2 + 1)
    for theta, c, ls in zip(THETAS, cols, ("-", "--", "-.")):
        p = np.array([np.exp(log_law((i, T2 - i), theta)) for i in k])
        assert abs(p.sum() - 1) < 1e-12
        a.plot(k, p * (T2 + 1), ls, color=c, lw=1.2, marker="o", ms=2.0,
               label=r"$\theta=%s$" % ("1/2" if theta == 0.5 else "%g" % theta))
    a.set_yscale("log")
    a.set_xlabel(r"visits to state $1$ in $T=%d$ steps" % T2)
    a.set_ylabel(r"$(T+1)\,\mathbb{P}(M_T=m)$")
    a.set_xticks([0, T2 // 2, T2])
    a.set_ylim(0.02, 12)
    a.set_yticks([0.1, 1, 10])
    a.legend(frameon=False, loc="lower center", handlelength=2.4)
    a.text(0.03, 0.95, "(a)", transform=a.transAxes, va="top")

    # Three states. The interior of the simplex, its edges and its corners are drawn apart.
    corner = {0: np.array([0.0, 0.0]), 1: np.array([0.5, sqrt(3) / 2]), 2: np.array([1.0, 0.0])}
    center = sum(corner.values()) / 3
    inner = [(i, j, T3 - i - j) for i in range(1, T3) for j in range(1, T3 - i)]
    tri = Triangulation([xy(m)[0] for m in inner], [xy(m)[1] for m in inner])
    nb = (T3 + 1) * (T3 + 2) // 2
    gap, width, radius, clip = 0.035, 0.05, 0.05, 0.7
    norm = plt.Normalize(-clip, clip)
    for ax, theta, letter in zip(axes[1:], (0.5, 2.0), "bc"):

        def level(m):
            return (log_law(m, theta) + log(nb)) / log(10)

        total = sum(10 ** level(m) for m in inner)
        z = np.clip([level(m) for m in inner], -clip, clip)
        pc = ax.tripcolor(tri, z, shading="gouraud", cmap=PALETTE, norm=norm, rasterized=True)
        ax.tricontour(tri, z, levels=[-0.6, -0.4, -0.2, 0.0, 0.2, 0.4, 0.6], colors="white", linestyles="solid",
                      linewidths=0.35, alpha=0.55)
        for missing in range(3):
            p, q = [k for k in range(3) if k != missing]
            along = corner[q] - corner[p]
            out = (corner[p] + corner[q]) / 2 - center
            out = out / np.linalg.norm(out)
            polys, vals = [], []
            for k in range(1, T3):
                m = [0, 0, 0]
                m[p], m[q] = T3 - k, k
                lo = corner[p] + along * (k - 0.5) / T3 + out * gap
                hi = corner[p] + along * (k + 0.5) / T3 + out * gap
                polys.append([lo, hi, hi + out * width, lo + out * width])
                vals.append(level(tuple(m)))
                total += 10 ** vals[-1]
            ax.add_collection(PolyCollection(polys, array=np.clip(vals, -clip, clip), cmap=PALETTE, norm=norm,
                                             edgecolors="face", linewidths=0.1))
        for k in range(3):
            m = [0, 0, 0]
            m[k] = T3
            out = corner[k] - center
            out = out / np.linalg.norm(out)
            v = level(tuple(m))
            total += 10 ** v
            ax.add_patch(Circle(corner[k] + out * (2 * gap + radius + 0.02), radius,
                                facecolor=PALETTE(norm(np.clip(v, -clip, clip))), edgecolor="0.3", linewidth=0.4))
        assert abs(total / nb - 1) < 1e-10
        ax.text(0.5, -0.27, r"(%s) $\theta=%s$" % (letter, "1/2" if theta == 0.5 else "2"),
                ha="center", va="top")
        ax.set_aspect("equal")
        ax.set_xlim(-0.2, 1.2)
        ax.set_ylim(-0.36, 1.1)
        ax.axis("off")
        print("theta = %g: corner/uniform = %.3g, center/uniform = %.3g"
              % (theta, 10 ** level((T3, 0, 0)), 10 ** level((T3 // 3,) * 3)))
    cb = fig.colorbar(pc, ax=list(axes[1:]), fraction=0.03, pad=0.02, ticks=[-0.5, 0, 0.5], extend="both")
    cb.set_label(r"$\log_{10}$ of probability / uniform")
    cb.outline.set_linewidth(0.4)
    dark_style.finish(fig)
    for ext, kw in (("pdf", {"dpi": 600}), ("png", {"dpi": 600})):
        fig.savefig(HERE / ("aging." + ext), **kw)
    plt.close(fig)
    print("wrote aging.pdf and aging.png")


if __name__ == "__main__":
    figure()
