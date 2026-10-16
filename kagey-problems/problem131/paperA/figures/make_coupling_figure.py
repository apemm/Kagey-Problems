"""Figure 5 of Paper A: the couplings at the central crossings and the boundary shift.

(a) The exact couplings J_N^P (periodic) and J_N^F (free) divided by log N, against log N, from
    the exact run polynomials, with the main terms of (eq:isingtemperature) and of Corollary 5.4(a)
    and the two approximations of Stepanyan et al. (their Eq. (16) and the fitted line of their
    Fig. 1(b)).
(b) The boundary shift N(u_N^P - u_N^F) against 1/log N for 10 <= N <= 10^9, with the first two
    terms log 2 + (1/4 - (1/2) log 2)/log N of (eq:boundaryshift).

The couplings and odds come from central_odds of verify_ising_coupling.py in the folder above
(bisection of the exact run polynomials in Decimal arithmetic at 80 digits, 220 halvings). The
plotted values are written to ../data/figures/fig_coupling.json.
Run:  python -B make_coupling_figure.py     (under a minute)
"""
import json
import sys
from decimal import localcontext
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
# Times text and STIX (Times-like) mathematics, as IOP recommends for figures
ss.plt.rcParams.update({"font.serif": ["Times New Roman", "STIXGeneral"], "mathtext.fontset": "stix"})
C0 = 0.5 * log(np.pi / 8)
CP = 0.5 * log(np.pi / 2)


def main_terms(L, c):
    LL = np.log(L)
    return (L - LL) / 2 + (LL / 4 - c / 2) / L


def main():
    ns = sorted({int(round(x)) for x in np.logspace(1, 9, 33)})
    with localcontext() as ctx:
        ctx.prec = 80
        up = [central_odds(n, periodic_ratio) for n in ns]
        uf = [central_odds(n, free_ratio) for n in ns]
        jp = np.array([float(coupling(u)) for u in up])
        jf = np.array([float(coupling(u)) for u in uf])
        shift = np.array([float(n * (p - f)) for n, p, f in zip(ns, up, uf)])
    Ln = np.log(np.array(ns, dtype=float))
    a6 = Ln <= np.log(1e6) + 1e-9           # panel (a) stops at 10^6, as Table 3 does
    L = np.linspace(np.log(10), np.log(1e6), 400)

    # Eq. (16)/log N = 2/5 - 1/(5 log N) increases toward 2/5, and the fitted line divided by
    # log N tends to 0.3864, so both stay below the limit 1/2 of the exact ratio.
    EQ16, FIT = ss.GOLD, "#6E6E6E"
    eq16 = lambda x: (2 * x - 1) / 5          # Eq. (16) of Stepanyan et al.
    fit = lambda x: 0.3864 * x - 0.21055      # the fitted line of their Fig. 1(b)

    fig, (ax, bx) = plt.subplots(1, 2, figsize=(ss.FULL, 2.5), gridspec_kw={"width_ratios": [1.2, 1]})
    c = ss.SERIES
    ax.axhline(0.5, color=c["grid"], lw=0.6)
    ax.text(13.6, 0.505, r"limit $\frac{1}{2}$", ha="right", va="bottom", color="#6E6E6E")
    lp, = ax.plot(L, main_terms(L, CP) / L, color=c["exact"], lw=1.1)
    lf, = ax.plot(L, main_terms(L, C0) / L, color=ss.PURPLE, lw=1.1)
    La, jpa, jfa = Ln[a6], jp[a6], jf[a6]
    mp, = ax.plot(La[::2], jpa[::2] / La[::2], "o", ms=3.2, color=c["exact"], mfc="white", mew=0.9)
    mf, = ax.plot(La[1::2], jfa[1::2] / La[1::2], "s", ms=2.8, color=ss.PURPLE, mew=0)
    le, = ax.plot(L, eq16(L) / L, color=EQ16, lw=1.1, ls=(0, (5, 3)))
    lt, = ax.plot(L, fit(L) / L, color=FIT, lw=1.1, ls=(0, (5, 3)))
    ax.legend([(lp, mp), (lf, mf), le, lt], ["periodic ends", "free ends", "Stepanyan formula", "Stepanyan fit"],
              loc="upper left", ncol=2, frameon=False, handlelength=2.2, columnspacing=0.9,
              handletextpad=0.5, borderaxespad=0.2)
    ax.set_xlabel(r"$\log N$")
    ax.set_xticks(range(2, 15, 2))
    ax.set_ylabel(r"$J/\log N$ at the crossing")
    ax.set_ylim(0.27, 0.66)
    ss.top_n_axis(ax, range(1, 7))
    ss.panel(ax, "a", x=0.97, y=0.05, ha="right", va="bottom")

    # (b) the boundary shift against 1/log N, with its first two terms
    x = 1 / Ln
    xx = np.linspace(0, 0.45, 200)
    bx.plot(xx, log(2) + (0.25 - 0.5 * log(2)) * xx, color=ss.INK, lw=0.8)
    bx.plot(x, shift, "o", ms=3.0, color=c["exact"], mfc="white", mew=0.9)
    bx.plot([0], [log(2)], "D", ms=3.2, color=ss.ACCENT)
    bx.annotate(r"$\log 2$", xy=(0, log(2)), xytext=(6, -11), textcoords="offset points", color=ss.ACCENT)
    bx.set_xlim(-0.01, 0.45)
    bx.set_xlabel(r"$1/\log N$")
    bx.set_ylabel(r"$N(u^{\rm P}_N-u^{\rm F}_N)$")
    ss.panel(bx, "b", x=0.96, y=0.95, ha="right", va="top")
    fig.tight_layout(w_pad=1.2)
    ss.save(fig, HERE / "coupling")

    dev = shift - (log(2) + (0.25 - 0.5 * log(2)) / Ln)
    print("boundary shift at N = 10, 10^3, 10^6, 10^9:",
          [round(float(shift[ns.index(n)]), 5) for n in (10, 1000, 10 ** 6, 10 ** 9)])
    print("minus the two terms:", [f"{float(dev[ns.index(n)]):.2e}" for n in (10, 1000, 10 ** 6, 10 ** 9)])
    out = HERE.parent / "data" / "figures"
    out.mkdir(parents=True, exist_ok=True)
    (out / "fig_coupling.json").write_text(json.dumps({
        "method": "central odds by Decimal bisection (80 digits, 220 halvings) of the exact run "
                  "polynomials, central_odds of verify_ising_coupling.py",
        "N": ns, "J_periodic": jp.tolist(), "J_free": jf.tolist(), "shift": shift.tolist()},
        indent=1) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
