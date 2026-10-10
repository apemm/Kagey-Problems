"""Figure `aging`: the exact law of the counts of the fresh-or-repeat chain.

The law is the one of Proposition `prop:aging-urn`,
    P(M_T = m) = T!/(d theta)^(T) * prod_i theta^(m_i)/m_i!,
where x^(m) is the rising factorial. Panel (a) is two states, and panels (b)
and (c) are three states on the simplex, colored by the probability of a bin
relative to the uniform law (which is the law at theta = 1).

Run:  python make_aging_figure.py     (a second)
"""
from math import lgamma, log, sqrt
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.collections import PolyCollection

HERE = Path(__file__).resolve().parent
FULL = 6.4
T2, T3 = 40, 36
THETAS = (0.5, 1.0, 2.0)

try:
    from cmcrameri import cm as _cmc
    PALETTE = _cmc.batlow
except ImportError:
    PALETTE = plt.get_cmap("viridis")

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
    cols = [PALETTE(x) for x in (0.78, 0.45, 0.05)]
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

    rad = 1.0 / (T3 * sqrt(3))
    ang = np.pi / 6 + np.arange(6) * np.pi / 3
    hexagon = rad * np.c_[np.cos(ang), np.sin(ang)]
    bins = [(i, j, T3 - i - j) for i in range(T3 + 1) for j in range(T3 + 1 - i)]
    nb = len(bins)
    for ax, theta, letter in zip(axes[1:], (0.5, 2.0), "bc"):
        z = np.array([(log_law(m, theta) + log(nb)) / log(10) for m in bins])
        assert abs(sum(10 ** v for v in z) / nb - 1) < 1e-10
        pc = PolyCollection([hexagon + xy(m) for m in bins], array=np.clip(z, -1.0, 1.0),
                            cmap=PALETTE, edgecolors="face", linewidths=0.15)
        pc.set_clim(-1.0, 1.0)
        ax.add_collection(pc)
        ax.text(0.5, -0.1, r"(%s) $\theta=%s$" % (letter, "1/2" if theta == 0.5 else "2"),
                ha="center", va="top")
        ax.set_aspect("equal")
        ax.set_xlim(-0.08, 1.08)
        ax.set_ylim(-0.22, 0.95)
        ax.axis("off")
        print("theta = %g: corner/uniform = %.3g, center/uniform = %.3g"
              % (theta, 10 ** z[bins.index((T3, 0, 0))], 10 ** z[bins.index((T3 // 3,) * 3)]))
    cb = fig.colorbar(pc, ax=list(axes[1:]), fraction=0.03, pad=0.02, ticks=[-1, 0, 1], extend="both")
    cb.set_label(r"$\log_{10}$ of probability / uniform")
    cb.outline.set_linewidth(0.4)
    for ext, kw in (("pdf", {}), ("png", {"dpi": 600})):
        fig.savefig(HERE / ("aging." + ext), **kw)
    plt.close(fig)
    print("wrote aging.pdf and aging.png")


if __name__ == "__main__":
    figure()
