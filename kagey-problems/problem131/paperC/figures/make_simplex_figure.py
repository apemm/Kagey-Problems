"""Figure `fig_simplex`: the law of the count vector on the simplex.

The chain is the path 1 - 2 - 3 with rate 1 on each edge, a uniform start and
transition matrix I + (T/N) Q. The law of the count vector is computed exactly
by a dynamic program over (n_1, n_2, current state). The three panels show it
at three values of T, with the mode on a vertex, on an edge and in the
interior.

Run:  python make_simplex_figure.py          (a few seconds)
      python make_simplex_figure.py --scan   (prints the face of the mode against T)
"""
import sys
from math import log, sqrt
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

HERE = Path(__file__).resolve().parent
FULL = 6.4
N = 48
Q = np.array([[-1.0, 1.0, 0.0], [1.0, -2.0, 1.0], [0.0, 1.0, -1.0]])
PANELS = (2.0, 5.5, 10.0)

import sys as _sys
_sys.path.insert(0, str(HERE.parent.parent / "figures"))
import dark_style  # black background and the manim palette, see figures/dark_style.py
PALETTE = dark_style.HEAT

plt.rcParams.update({
    "font.size": 8, "axes.labelsize": 8, "legend.fontsize": 8,
    "xtick.labelsize": 8, "ytick.labelsize": 8,
    "font.family": "serif", "mathtext.fontset": "cm",
    "axes.linewidth": 0.6, "lines.linewidth": 1.0,
    "savefig.bbox": "tight", "savefig.pad_inches": 0.02,
    "pdf.fonttype": 42,
})


def count_law(T, n=N):
    """P[n1, n2] = P(count vector = (n1, n2, n - n1 - n2)), exactly."""
    P = np.eye(3) + (T / n) * Q
    A = np.zeros((n + 1, n + 1, 3))
    A[1, 0, 0] = A[0, 1, 1] = A[0, 0, 2] = 1.0 / 3
    for _ in range(n - 1):
        B = np.zeros_like(A)
        into = A @ P                     # mass arriving in each state
        B[1:, :, 0] += into[:-1, :, 0]
        B[:, 1:, 1] += into[:, :-1, 1]
        B[:, :, 2] += into[:, :, 2]
        A = B
    return A.sum(axis=2)


def mode_of(law, n=N):
    i, j = np.unravel_index(np.argmax(law), law.shape)
    return int(i), int(j), n - int(i) - int(j)


def face(m):
    return "".join(str(k + 1) for k in range(3) if m[k] > 0)


def xy(n1, n2, n3):
    """State 1 at the lower left, state 2 on top, state 3 at the lower right."""
    s = n1 + n2 + n3
    return (n3 + 0.5 * n2) / s, (sqrt(3) / 2) * n2 / s


def scan():
    L = log(N)
    print("N = %d, log N = %.3f; first order: vertex to pair at tau = %.3f, pair to all at tau = %.3f"
          % (N, L, 2 / (sqrt(5) - 1), 2 / (3 - sqrt(5))))
    last = None
    for T in np.arange(0.5, 24.01, 0.25):
        law = count_law(T)
        m = mode_of(law)
        f = face(m)
        if f != last:
            print("T = %5.2f (tau = %.2f): mode %s on face {%s}" % (T, T / L, m, f))
            last = f


def figure():
    from matplotlib.collections import PolyCollection
    fig, axes = plt.subplots(1, 3, figsize=(FULL, 2.2))
    idx = [(i, j) for i in range(N + 1) for j in range(N + 1 - i)]
    X = np.array([xy(i, j, N - i - j)[0] for i, j in idx])
    Y = np.array([xy(i, j, N - i - j)[1] for i, j in idx])
    rad = 1.0 / (N * sqrt(3))            # hexagons that tile the triangle
    ang = np.pi / 6 + np.arange(6) * np.pi / 3
    hexagon = rad * np.c_[np.cos(ang), np.sin(ang)]
    floor = -3.0
    for ax, T, letter in zip(axes, PANELS, "abc"):
        law = count_law(T)
        assert abs(law.sum() - 1) < 1e-10
        vals = np.array([law[i, j] for i, j in idx])
        with np.errstate(divide="ignore"):
            z = np.log10(vals / vals.max())
        keep = np.isfinite(z)            # bins of probability zero stay white
        polys = [hexagon + (x, y) for x, y, k in zip(X, Y, keep) if k]
        pc = PolyCollection(polys, array=np.maximum(z[keep], floor), cmap=PALETTE,
                            edgecolors="face", linewidths=0.15)
        pc.set_clim(floor, 0.0)
        ax.add_collection(pc)
        o = 2 * rad
        ax.plot([-o, 1 + o, 0.5, -o], [-o / sqrt(3), -o / sqrt(3), sqrt(3) / 2 + 2 * o / sqrt(3), -o / sqrt(3)],
                color="0.45", lw=0.5)
        m = mode_of(law)
        # the law is symmetric under 1 <-> 3, so on the boundary mark the mirror image too
        marks = {m} if min(m) > 0 else {m, (m[2], m[1], m[0])}
        for mm in marks:
            ax.plot(*xy(*mm), marker="o", ms=6.5, mfc="none", mec="white", mew=2.0, clip_on=False)
            ax.plot(*xy(*mm), marker="o", ms=6.5, mfc="none", mec="black", mew=0.8, clip_on=False)
        ax.text(-0.05, -0.04, "$1$", ha="right", va="top")
        ax.text(1.05, -0.04, "$3$", ha="left", va="top")
        ax.text(0.5, sqrt(3) / 2 + 0.05, "$2$", ha="center", va="bottom")
        ax.text(0.5, -0.1, "(%s) $T=%g$" % (letter, T), ha="center", va="top")
        ax.set_aspect("equal")
        ax.set_xlim(-0.1, 1.1)
        ax.set_ylim(-0.22, 1.0)
        ax.axis("off")
        print("T = %g: mode %s on face {%s}, P(mode) = %.3e" % (T, m, face(m), law[m[0], m[1]]))
    cb = fig.colorbar(pc, ax=list(axes), fraction=0.018, pad=0.02, ticks=[-3, -2, -1, 0],
                      extend="min")
    cb.set_label(r"$\log_{10}(P_N(n)/\max P_N)$")
    cb.outline.set_linewidth(0.4)
    dark_style.finish(fig)
    for ext, kw in (("pdf", {}), ("png", {"dpi": 600})):
        fig.savefig(HERE / ("fig_simplex." + ext), **kw)
    plt.close(fig)
    print("wrote fig_simplex.pdf and fig_simplex.png")


if __name__ == "__main__":
    if "--scan" in sys.argv:
        scan()
    else:
        figure()
