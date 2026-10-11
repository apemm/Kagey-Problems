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
N = 90
FLOOR = -4.0
Q = np.array([[-1.0, 1.0, 0.0], [1.0, -2.0, 1.0], [0.0, 1.0, -1.0]])
PANELS = (2.0, 5.5, 10.0)

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
    """The interior of the simplex, its three edges and its three corners are
    drawn apart, on one color scale. So one sees on which face the mass sits."""
    from matplotlib.collections import PolyCollection
    from matplotlib.patches import Circle
    from matplotlib.tri import Triangulation
    fig, axes = plt.subplots(1, 3, figsize=(FULL, 2.25))
    corner = {0: np.array([0.0, 0.0]), 1: np.array([0.5, sqrt(3) / 2]), 2: np.array([1.0, 0.0])}
    center = sum(corner.values()) / 3
    inner = [(i, j) for i in range(1, N) for j in range(1, N - i)]
    X = np.array([xy(i, j, N - i - j)[0] for i, j in inner])
    Y = np.array([xy(i, j, N - i - j)[1] for i, j in inner])
    tri = Triangulation(X, Y)
    gap, width, radius = 0.035, 0.05, 0.05
    floor = FLOOR
    norm = plt.Normalize(floor, 0.0)
    for ax, T, letter in zip(axes, PANELS, "abc"):
        law = count_law(T)
        assert abs(law.sum() - 1) < 1e-10
        top = law.max()

        def level(i, j):
            return max(np.log10(law[i, j] / top), floor)

        # the interior, smoothly shaded, with a contour at each power of ten
        z = np.array([level(i, j) for i, j in inner])
        pc = ax.tripcolor(tri, z, shading="gouraud", cmap=PALETTE, norm=norm, rasterized=True)
        ax.tricontour(tri, z, levels=np.arange(floor + 1, 0), colors="white", linewidths=0.35, alpha=0.55)
        # the three edges, as bands outside the triangle
        mass = {"in": sum(law[i, j] for i, j in inner)}
        for missing in range(3):
            p, q = [k for k in range(3) if k != missing]
            along = corner[q] - corner[p]
            out = (corner[p] + corner[q]) / 2 - center
            out = out / np.linalg.norm(out)
            polys, vals, tot = [], [], 0.0
            for k in range(1, N):
                n = [0, 0, 0]
                n[p], n[q] = N - k, k
                lo = corner[p] + along * (k - 0.5) / N + out * gap
                hi = corner[p] + along * (k + 0.5) / N + out * gap
                polys.append([lo, hi, hi + out * width, lo + out * width])
                vals.append(level(n[0], n[1]))
                tot += law[n[0], n[1]]
            mass["".join(str(k + 1) for k in (p, q))] = tot
            if tot == 0:                  # no edge between the two states, so no mass here
                a0, a1 = corner[p] + along * 0.5 / N + out * gap, corner[p] + along * (N - 0.5) / N + out * gap
                ax.add_collection(PolyCollection([[a0, a1, a1 + out * width, a0 + out * width]],
                                                 facecolors="none", edgecolors="0.6", linewidths=0.5,
                                                 linestyles="--"))
                continue
            ax.add_collection(PolyCollection(polys, array=np.array(vals), cmap=PALETTE, norm=norm,
                                             edgecolors="face", linewidths=0.1))
        # the three corners, as disks
        for k in range(3):
            n = [0, 0, 0]
            n[k] = N
            out = corner[k] - center
            out = out / np.linalg.norm(out)
            c = corner[k] + out * (2 * gap + radius + 0.02)
            ax.add_patch(Circle(c, radius, facecolor=PALETTE(norm(level(n[0], n[1]))), edgecolor="0.3",
                                linewidth=0.4))
            mass[str(k + 1)] = law[n[0], n[1]]
            ax.annotate("$%d$" % (k + 1), c + out * (radius + 0.075), ha="center", va="center")
        assert abs(sum(mass.values()) - 1) < 1e-10
        # the mode (the law is symmetric under 1 <-> 3, so mark the mirror image too)
        m = mode_of(law)
        for mm in ({m} if min(m) > 0 else {m, (m[2], m[1], m[0])}):
            zero = [k for k in range(3) if mm[k] == 0]
            pos = np.array(xy(*mm))
            if len(zero) == 1:
                out = (sum(corner[k] for k in range(3) if k != zero[0])) / 2 - center
                pos = pos + out / np.linalg.norm(out) * (gap + width / 2)
            elif len(zero) == 2:
                k = [k for k in range(3) if mm[k] > 0][0]
                out = corner[k] - center
                pos = corner[k] + out / np.linalg.norm(out) * (2 * gap + radius + 0.02)
            ax.plot(*pos, marker="o", ms=4.6 if len(zero) < 2 else 9.6, mfc="none", mec="white", mew=1.7)
            ax.plot(*pos, marker="o", ms=4.6 if len(zero) < 2 else 9.6, mfc="none", mec="black", mew=0.7)
        ax.text(0.5, -0.27, "(%s) $T=%g$" % (letter, T), ha="center", va="top")
        ax.set_aspect("equal")
        ax.set_xlim(-0.23, 1.23)
        ax.set_ylim(-0.36, 1.2)
        ax.axis("off")
        print("T = %g: mode %s on face {%s}, P(mode) = %.3e" % (T, m, face(m), law[m[0], m[1]]))
        print("   mass: corners %.3f, edges 12 %.3f, 23 %.3f, 13 %.3f, interior %.3f"
              % (mass["1"] + mass["2"] + mass["3"], mass["12"], mass["23"], mass["13"], mass["in"]))
    cb = fig.colorbar(pc, ax=list(axes), fraction=0.018, pad=0.02, ticks=np.arange(floor, 1),
                      extend="min")
    cb.set_label(r"$\log_{10}(P_N(n)/\max P_N)$")
    cb.outline.set_linewidth(0.4)
    dark_style.finish(fig)
    for ext, kw in (("pdf", {"dpi": 600}), ("png", {"dpi": 600})):
        fig.savefig(HERE / ("fig_simplex." + ext), **kw)
    plt.close(fig)
    print("wrote fig_simplex.pdf and fig_simplex.png")


if __name__ == "__main__":
    if "--scan" in sys.argv:
        scan()
    else:
        figure()
