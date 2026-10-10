"""Figure `fig_sleep` for the sleep application (run sleep_application.py --boot B first).

(a) One night as a hypnogram, the usual display of scored sleep.
(b) The time budgets of all windows on the simplex. This is all the data the
    fit from budgets sees. Time budgets are compositional data, and the ternary
    diagram is their usual display.
(c) The flows of the chain fitted to the full sequences, per 1000 epochs.
(d) Two-way flows and the net flow, from the full sequences and from the
    budgets alone, with bootstrap intervals over nights.
(e) How long a waking bout lasts, against the geometric law that a Markov chain
    forces. Brief awakenings are known to have heavy tails (Lo et al. 2004).
"""
import json
import sys
from math import sqrt
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.collections import PolyCollection
from matplotlib.patches import FancyArrowPatch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "figures"))
import dark_style as ds
import sleep_data as sd

FULL = 6.4
COL = [ds.YELLOW, ds.BLUE, ds.RED]          # awake, non-REM, REM
plt.rcParams.update({
    "font.size": 8, "axes.labelsize": 8, "legend.fontsize": 7.5,
    "xtick.labelsize": 8, "ytick.labelsize": 8,
    "font.family": "serif", "mathtext.fontset": "cm",
    "axes.linewidth": 0.6, "lines.linewidth": 1.0,
    "xtick.direction": "in", "ytick.direction": "in",
    "savefig.bbox": "tight", "savefig.pad_inches": 0.02,
    "pdf.fonttype": 42,
})


def tern(k):
    """Awake at the lower left, non-REM on top, REM at the lower right."""
    s = k.sum()
    return (k[2] + 0.5 * k[1]) / s, (sqrt(3) / 2) * k[1] / s


def main():
    res = json.loads((sd.DATA / "results.json").read_text(encoding="utf-8"))
    NW = res["epochs_per_window"]
    win = sd.windows(NW)
    fig = plt.figure(figsize=(FULL, 4.9))
    gs = fig.add_gridspec(2, 12, height_ratios=[0.9, 1.15], hspace=0.5, wspace=0.6)

    # (a) a hypnogram
    ax = fig.add_subplot(gs[0, :8])
    name, x = sd.nights()[3]
    t = np.arange(len(x)) * sd.EPOCH / 3600.0
    level = {0: 2, 2: 1, 1: 0}                 # awake on top, then REM, then non-REM
    y = np.array([level.get(v, np.nan) for v in x], dtype=float)
    ax.step(t, y, where="post", color="0.55", lw=0.6)
    for s in range(3):
        m = x == s
        ax.plot(t[m], y[m], "s", ms=1.6, color=COL[s], mew=0)
    ax.set_yticks([0, 1, 2])
    ax.set_yticklabels(["non-REM", "REM", "awake"])
    ax.set_ylim(-0.35, 2.35)
    ax.set_xlim(0, t[-1])
    ax.set_xlabel("hours after lights off")
    ax.text(0.99, 0.93, "(a) one night", transform=ax.transAxes, ha="right", va="top")

    # (b) the budgets on the simplex
    ax = fig.add_subplot(gs[0, 8:])
    K = np.array([np.bincount(w, minlength=3) for _, w in win])
    cells, mult = np.unique(K, axis=0, return_counts=True)
    rad = 1.0 / (NW * sqrt(3))
    ang = np.pi / 6 + np.arange(6) * np.pi / 3
    hexagon = 1.9 * rad * np.c_[np.cos(ang), np.sin(ang)]
    pc = PolyCollection([hexagon + tern(k) for k in cells], array=np.log10(mult),
                        cmap=ds.HEAT, edgecolors="face", linewidths=0.1)
    pc.set_clim(-0.6, np.log10(mult.max()))
    ax.add_collection(pc)
    o = 0.03
    ax.plot([-o, 1 + o, 0.5, -o], [-o / sqrt(3), -o / sqrt(3), sqrt(3) / 2 + 2 * o / sqrt(3), -o / sqrt(3)],
            color="0.45", lw=0.5)
    ax.text(-0.04, -0.07, "awake", ha="left", va="top")
    ax.text(1.04, -0.07, "REM", ha="right", va="top")
    ax.text(0.5, sqrt(3) / 2 + 0.07, "non-REM", ha="center", va="bottom")
    ax.set_aspect("equal")
    ax.set_xlim(-0.12, 1.12)
    ax.set_ylim(-0.3, 1.05)
    ax.axis("off")
    ax.text(0.5, -0.2, "(b) %d time budgets" % len(K), ha="center", va="top")

    # (c) the flows from the full sequences
    ax = fig.add_subplot(gs[1, :4])
    P = np.array(res["point"]["paths"]["P"])
    pi = np.array(res["point"]["paths"]["pi"])
    f = 1000 * pi[:, None] * P
    pos = {0: (0.0, 0.0), 1: (0.6, 1.05), 2: (1.2, 0.0)}
    for i in range(3):
        for j in range(3):
            if i == j:
                continue
            ax.add_patch(FancyArrowPatch(pos[i], pos[j], connectionstyle="arc3,rad=0.2",
                                         arrowstyle="-|>", mutation_scale=5 + 0.5 * f[i, j],
                                         lw=0.35 + 0.13 * f[i, j], shrinkA=12, shrinkB=12,
                                         color=COL[i], zorder=1))
            mx, my = 0.5 * (pos[i][0] + pos[j][0]), 0.5 * (pos[i][1] + pos[j][1])
            dx, dy = pos[j][0] - pos[i][0], pos[j][1] - pos[i][1]
            nrm = sqrt(dx * dx + dy * dy)
            ax.text(mx + 0.27 * dy / nrm - 0.16 * dx, my - 0.27 * dx / nrm - 0.16 * dy, "%.1f" % f[i, j], ha="center", va="center",
                    fontsize=7, color=COL[i])
    for i, lab in enumerate(("awake", "non-\nREM", "REM")):
        ax.plot(*pos[i], "o", ms=19, mfc="white", mec=COL[i], mew=1.2, zorder=3)
        ax.text(*pos[i], lab, ha="center", va="center", fontsize=6.5, zorder=4, linespacing=0.9)
    ax.set_xlim(-0.35, 1.55)
    ax.set_ylim(-0.5, 1.35)
    ax.set_aspect("equal")
    ax.axis("off")
    ax.text(0.6, -0.4, "(c) flows per 1000 epochs", ha="center", va="top")

    # (d) estimates with bootstrap intervals
    ax = fig.add_subplot(gs[1, 4:8])
    labels = [r"$c$ awake, non-REM", r"$c$ awake, REM", r"$c$ non-REM, REM", r"net flow $|J|$"]

    def row(d, kind):
        c = [1000 * v for v in d[kind]["c"]]
        if kind == "paths":
            return c + [1000 * abs(float(np.mean(d[kind]["J"])))]
        return c + [1000 * d[kind]["absj"]]

    boots = res.get("boot", [])
    for kind, col, dy, lab in (("paths", ds.BLUE, 0.14, "full sequences"), ("budgets", ds.YELLOW, -0.14, "budgets only")):
        pt = row(res["point"], kind)
        ys = np.arange(4)[::-1] + dy
        if boots:
            bb = np.array([row(b, kind) for b in boots])
            lo, hi = np.percentile(bb, [5, 95], axis=0)
            ax.hlines(ys, np.maximum(lo, 0.15), hi, color=col, lw=1.2)
        ax.plot(pt, ys, "o", ms=3.8, color=col, label=lab)
    ax.set_xscale("log")
    ax.set_xlim(0.12, 80)
    ax.set_yticks([])
    for k, lab in enumerate(labels):
        ax.text(0.14, 3 - k + 0.32, lab, fontsize=7, va="center", ha="left")
    ax.set_ylim(-0.6, 5.2)
    ax.set_xlabel("per 1000 epochs")
    ax.legend(frameon=False, loc="upper right", handlelength=1.0, borderpad=0.1, ncol=1)
    ax.text(0.03, 0.97, "(d)", transform=ax.transAxes, ha="left", va="top")

    # (e) waking bouts against the geometric law
    ax = fig.add_subplot(gs[1, 9:])
    bouts = []
    for _, x in sd.nights():
        asleep = np.flatnonzero(x > 0)
        x = x[asleep[0]:asleep[-1] + 1]
        run = 0
        for v in x:
            if v == 0:
                run += 1
            else:
                if run:
                    bouts.append(run)
                run = 0
    bouts = np.array(bouts)
    ks = np.arange(1, bouts.max() + 1)
    surv = np.array([(bouts >= k).mean() for k in ks])
    ax.plot(ks * sd.EPOCH / 60.0, surv, "o", ms=2.6, color=ds.YELLOW, label="data")
    stay = P[0, 0]
    ax.plot(ks * sd.EPOCH / 60.0, stay ** (ks - 1), "-", color="0.5", lw=1.0, label="Markov chain")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_ylim(8e-4, 1.5)
    ax.set_xlabel("waking bout (min)")
    ax.set_ylabel("share at least this long", fontsize=7)
    ax.legend(frameon=False, loc="lower left", handlelength=1.2, borderpad=0.1)
    ax.text(0.97, 0.95, "(e)", transform=ax.transAxes, ha="right", va="top")
    print("waking bouts: %d, mean %.2f epochs, longest %d; Markov mean %.2f" % (len(bouts), bouts.mean(), bouts.max(), 1 / (1 - stay)))
    print("share of waking bouts of one epoch: data %.3f, Markov %.3f" % ((bouts == 1).mean(), 1 - stay))
    print("share at least 20 epochs: data %.4f, Markov %.5f" % ((bouts >= 20).mean(), stay ** 19))

    ds.finish(fig)
    fig.savefig(HERE / "fig_sleep.pdf")
    fig.savefig(HERE / "fig_sleep.png", dpi=400)
    print("wrote fig_sleep")


if __name__ == "__main__":
    main()
