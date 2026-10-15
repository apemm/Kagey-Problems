"""The shared figure style of the Problem 131 papers (provisional, October 2026).

One module for every figure script of the series, so that the papers look like a family:
white background, serif math in the font of the text, sizes set to the printed width so that
8 pt in the script is 8 pt on the page, and one meaning per color.

  use()            set the rcParams
  FULL, COL        the text width and the column width of the papers, in inches
  SERIES           semantic colors: "exact" (blue) for the results of the paper, "prior" and
                   "prior2" (greys) for earlier work and approximations, "accent" (vermilion) only
                   for the crossing or threshold case, "grid" for guides, "ink" for text
  shades(n)        n colors along the series gradient (purple, blue, teal, green, gold)
  panel(ax, ...)   panel letters "(a)", "(b)" in the same place and size everywhere
  top_n_axis(ax)   a top axis in N for a plot against log N
  save(fig, path)  vector PDF with embedded TrueType fonts and a 600 dpi PNG
"""
from math import log
from pathlib import Path

import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap

FULL, COL = 6.4, 3.37

# the light version of the series gradient (figures/dark_style.light())
PURPLE, BLUE, TEAL, GREEN, GOLD = "#7A4F92", "#1C8FB0", "#2E9C82", "#5F9A45", "#C77F2A"
INK = "#1F2328"
GRADIENT = LinearSegmentedColormap.from_list("series", [PURPLE, BLUE, TEAL, GREEN, GOLD])
ACCENT = "#D55E00"   # vermilion (Okabe-Ito), only for the crossing or threshold case
SERIES = {"exact": BLUE, "prior": "#8C8C8C", "prior2": "#B0B0B0", "accent": ACCENT, "grid": "#BDBDBD",
          "ink": INK}


def use():
    plt.rcParams.update({
        "font.size": 8, "axes.labelsize": 8, "legend.fontsize": 8,
        "xtick.labelsize": 8, "ytick.labelsize": 8,
        "font.family": "serif", "font.serif": ["CMU Serif", "Computer Modern Roman", "DejaVu Serif"],
        "mathtext.fontset": "cm",
        "axes.linewidth": 0.6, "lines.linewidth": 1.0,
        "axes.edgecolor": INK, "text.color": INK, "axes.labelcolor": INK,
        "xtick.color": INK, "ytick.color": INK,
        "xtick.direction": "in", "ytick.direction": "in",
        "xtick.top": True, "ytick.right": True,
        "xtick.major.size": 3, "ytick.major.size": 3, "xtick.minor.size": 1.5, "ytick.minor.size": 1.5,
        "savefig.bbox": "tight", "savefig.pad_inches": 0.02,
        "pdf.fonttype": 42, "ps.fonttype": 42,
        "figure.facecolor": "white", "axes.facecolor": "white",
    })


def shades(n, lo=0.0, hi=1.0):
    if n == 1:
        return [GRADIENT(lo)]
    return [GRADIENT(lo + (hi - lo) * i / (n - 1)) for i in range(n)]


def panel(ax, letter, x=0.03, y=0.95, ha="left", va="top"):
    ax.text(x, y, f"({letter})", transform=ax.transAxes, ha=ha, va=va)


def top_n_axis(ax, exponents):
    """Label the top edge of a plot against log N with powers of ten."""
    lo, hi = ax.get_xlim()
    top = ax.twiny()
    top.set_xlim(lo, hi)
    top.set_xticks([e * log(10) for e in exponents])
    top.set_xticklabels([rf"$10^{e}$" for e in exponents])
    top.tick_params(direction="in", length=3, pad=1.5)
    top.set_xlabel(r"$N$", labelpad=2)
    ax.tick_params(top=False)
    return top


def save(fig, path):
    path = Path(path)
    fig.savefig(path.with_suffix(".pdf"))
    fig.savefig(path.with_suffix(".png"), dpi=600)
    plt.close(fig)
    print(f"wrote {path.name}.pdf and .png")
