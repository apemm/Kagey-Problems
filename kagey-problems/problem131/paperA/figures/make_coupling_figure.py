"""Figure 5 of Paper A: the coupling at the central crossings against log N.

(a) The exact couplings J_N^P (periodic) and J_N^F (free) from the exact run polynomials, the
    main terms of (eq:isingtemperature) and of Corollary 5.4(a), and the two approximations of
    Stepanyan et al. (their Eq. (16) and the fitted line of their Fig. 1(b)).
(b) Each approximation of the periodic coupling minus the exact value.

The couplings come from verify_ising_coupling.py in the folder above (Decimal, 80 digits).
Run:  python -B make_coupling_figure.py     (a few seconds)
"""
import sys
from decimal import Decimal as D, localcontext
from math import log
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE.parent.parent / "figures"))
import series_style as ss  # noqa: E402  the shared style of the series
from verify_allbin import ratio as free_ratio  # noqa: E402
from verify_periodic_window import periodic_ratio  # noqa: E402
from verify_ising_coupling import central_odds, coupling  # noqa: E402

ss.use()
C0 = 0.5 * log(np.pi / 8)
CP = 0.5 * log(np.pi / 2)


def main_terms(L, c):
    LL = np.log(L)
    return (L - LL) / 2 + (LL / 4 - c / 2) / L


def main():
    ns = sorted({int(round(x)) for x in np.logspace(1, 6, 26)})
    with localcontext() as ctx:
        ctx.prec = 80
        jp = np.array([float(coupling(central_odds(n, periodic_ratio))) for n in ns])
        jf = np.array([float(coupling(central_odds(n, free_ratio))) for n in ns])
    Ln = np.log(np.array(ns, dtype=float))
    L = np.linspace(np.log(10), np.log(1e6), 400)

    fig, (ax, bx) = plt.subplots(1, 2, figsize=(ss.FULL, 2.45), gridspec_kw={"width_ratios": [1.25, 1]})
    c = ss.SERIES
    ax.plot(L, main_terms(L, CP), color=c["exact"], lw=1.1, label="main terms, periodic")
    ax.plot(L, main_terms(L, C0), color=c["exact"], lw=1.1, ls=(0, (4, 1.6)), label="main terms, free")
    ax.plot(Ln, jp, "o", ms=3.0, color=c["exact"], mfc="white", mew=0.9, label=r"exact $J_N^{\rm P}$")
    ax.plot(Ln, jf, "s", ms=2.6, color=c["exact"], mew=0, label=r"exact $J_N^{\rm F}$")
    ax.plot(L, (2 * L - 1) / 5, color=c["prior"], lw=1.0, ls=(0, (1, 1.3)), label="Stepanyan Eq. (16)")
    ax.plot(L, 0.3864 * L - 0.21055, color=c["prior2"], lw=1.0, ls=(0, (5, 1.5, 1, 1.5)), label="Stepanyan fit")
    ax.set_xlabel(r"$\log N$")
    ax.set_ylabel(r"coupling $J$ at the crossing")
    ss.top_n_axis(ax, range(1, 7))
    ax.set_ylim(0.4, 8.6)   # headroom for the legend
    ax.legend(loc="upper left", ncol=2, frameon=False, handlelength=1.8, columnspacing=0.9,
              handletextpad=0.5, borderaxespad=0.2, fontsize=7)
    ss.panel(ax, "a", x=0.96, y=0.06, ha="right", va="bottom")

    bx.axhline(0, color="0.6", lw=0.5)
    bx.plot(Ln, main_terms(Ln, CP) - jp, "-", color=c["exact"], lw=1.1)
    bx.plot(Ln, (2 * Ln - 1) / 5 - jp, color=c["prior"], lw=1.0, ls=(0, (1, 1.3)))
    bx.plot(Ln, 0.3864 * Ln - 0.21055 - jp, color=c["prior2"], lw=1.0, ls=(0, (5, 1.5, 1, 1.5)))
    # direct labels, each placed beside its own curve
    i = int(np.argmin(abs(Ln - 10.0)))
    bx.annotate("main terms", xy=(Ln[i], main_terms(Ln, CP)[i] - jp[i]), xytext=(0, 5),
                textcoords="offset points", ha="center", va="bottom", color=c["exact"])
    j = int(np.argmin(abs(Ln - 10.5)))
    bx.annotate("Eq. (16)", xy=(Ln[j], (2 * Ln[j] - 1) / 5 - jp[j]), xytext=(4, 2),
                textcoords="offset points", ha="left", va="bottom", color=c["prior"])
    bx.annotate("fit", xy=(Ln[j], 0.3864 * Ln[j] - 0.21055 - jp[j]), xytext=(-4, -3),
                textcoords="offset points", ha="right", va="top", color=c["prior"])
    bx.set_xlabel(r"$\log N$")
    bx.set_ylabel(r"approximation $-$ exact $J_N^{\rm P}$")
    ss.top_n_axis(bx, range(1, 7))
    ss.panel(bx, "b", x=0.04, y=0.06, ha="left", va="bottom")
    fig.tight_layout(w_pad=1.2)
    ss.save(fig, HERE / "coupling")


if __name__ == "__main__":
    main()
