"""Figure 5 of Paper A: the coupling at the central crossings, divided by log N, against log N.

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

    # One color per curve, all lines solid, so that no two curves differ only by dash pattern.
    EQ16, FIT = ss.GOLD, "#6E6E6E"
    eq16 = lambda x: (2 * x - 1) / 5          # Eq. (16) of Stepanyan et al.
    fit = lambda x: 0.3864 * x - 0.21055      # the fitted line of their Fig. 1(b)

    fig, (ax, bx) = plt.subplots(1, 2, figsize=(ss.FULL, 2.45), gridspec_kw={"width_ratios": [1.25, 1]})
    c = ss.SERIES
    # (a) J / log N, which separates the curves: the exact coupling climbs toward 1/2,
    # while both approximations level off below 2/5
    ax.axhline(0.5, color=c["grid"], lw=0.6)
    ax.text(13.6, 0.505, r"limit $\frac{1}{2}$", ha="right", va="bottom", color="#6E6E6E", fontsize=7)
    lp, = ax.plot(L, main_terms(L, CP) / L, color=c["exact"], lw=1.1)
    lf, = ax.plot(L, main_terms(L, C0) / L, color=ss.PURPLE, lw=1.1)
    mp, = ax.plot(Ln[::2], jp[::2] / Ln[::2], "o", ms=3.2, color=c["exact"], mfc="white", mew=0.9)
    mf, = ax.plot(Ln[1::2], jf[1::2] / Ln[1::2], "s", ms=2.8, color=ss.PURPLE, mew=0)
    le, = ax.plot(L, eq16(L) / L, color=EQ16, lw=1.1)
    lt, = ax.plot(L, fit(L) / L, color=FIT, lw=1.1)
    ax.legend([(lp, mp), (lf, mf), le, lt], ["periodic ends", "free ends", "Stepanyan Eq. (16)", "Stepanyan fit"],
              loc="upper left", ncol=2, frameon=False, handlelength=2.0, columnspacing=0.9,
              handletextpad=0.5, borderaxespad=0.2, fontsize=7)
    ax.set_xlabel(r"$\log N$")
    ax.set_xticks(range(2, 15, 2))
    ax.set_ylabel(r"$J/\log N$ at the crossing")
    ax.set_ylim(0.27, 0.64)
    ss.top_n_axis(ax, range(1, 7))
    ss.panel(ax, "a", x=0.97, y=0.05, ha="right", va="bottom")

    # (b) each approximation of the periodic coupling minus the exact value, labeled in place
    bx.axhline(0, color=c["grid"], lw=0.6)
    dm = main_terms(Ln, CP) - jp
    bx.plot(Ln, dm, "-", color=c["exact"], lw=1.1)
    bx.plot(Ln[::2], dm[::2], "o", ms=2.6, color=c["exact"], mfc="white", mew=0.8)
    bx.plot(Ln, eq16(Ln) - jp, color=EQ16, lw=1.1)
    bx.plot(Ln, fit(Ln) - jp, color=FIT, lw=1.1)
    i = int(np.argmin(abs(Ln - 10.0)))
    bx.annotate("main terms", xy=(Ln[i], dm[i]), xytext=(0, 5),
                textcoords="offset points", ha="center", va="bottom", color=c["exact"])
    j = int(np.argmin(abs(Ln - 10.5)))
    bx.annotate("Eq. (16)", xy=(Ln[j], eq16(Ln[j]) - jp[j]), xytext=(5, 2),
                textcoords="offset points", ha="left", va="bottom", color=EQ16)
    bx.annotate("fit", xy=(Ln[j], fit(Ln[j]) - jp[j]), xytext=(-5, -3),
                textcoords="offset points", ha="right", va="top", color=FIT)
    bx.set_xlabel(r"$\log N$")
    bx.set_xticks(range(2, 15, 2))
    bx.set_ylabel(r"approximation $-$ exact $J_N^{\rm P}$")
    ss.top_n_axis(bx, range(1, 7))
    ss.panel(bx, "b", x=0.04, y=0.05, ha="left", va="bottom")
    fig.tight_layout(w_pad=1.2)
    ss.save(fig, HERE / "coupling")


if __name__ == "__main__":
    main()
