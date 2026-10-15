"""Figure 2 of Paper D: one elephant walk and its memory tree (Lemma 3.1).

(a) The position of the walk against the step, with the steps that disagree with the first
    step drawn in blue.
(b) The random recursive tree of the same walk: step k+1 copies step U_k, drawn as an arc from
    U_k to k+1. Arcs in vermilion are flips. A step disagrees with the first step exactly when
    the path from it to step 1 crosses an odd number of flips, so each flip turns its whole
    family (Lemma `lem:tree`).

The walk is a fixed draw (seed below) chosen so that the first flip is early and the figure shows
a large family next to small ones. Run:  python -B make_family_figure.py   (under a second)
"""
import sys
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import Arc

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent / "figures"))
import series_style as ss  # noqa: E402

ss.use()
N, EPS, SEED = 40, 0.07, 89


def draw(seed):
    rng = np.random.default_rng(seed)
    parent = np.zeros(N + 1, dtype=int)
    mark = np.zeros(N + 1, dtype=int)
    sigma = np.zeros(N + 1, dtype=int)
    for k in range(1, N):                       # vertex k+1 picks a uniform parent in [k]
        parent[k + 1] = rng.integers(1, k + 1)
        mark[k + 1] = rng.random() < EPS
        sigma[k + 1] = sigma[parent[k + 1]] + mark[k + 1]
    return parent, mark, sigma


def family(parent, v):
    fam = {v}
    for k in range(v + 1, N + 1):
        if parent[k] in fam:
            fam.add(k)
    return fam


def main():
    parent, mark, sigma = draw(SEED)
    marks = [v for v in range(2, N + 1) if mark[v]]
    assert 2 <= len(marks) <= 4 and marks[0] <= 6, marks     # the reason for the seed
    odd = sigma % 2 == 1
    X = np.where(odd[1:], -1, 1)                             # X_1 = +1
    S = np.concatenate(([0], np.cumsum(X)))
    big = family(parent, marks[0])
    # Lemma tree: the odd vertices are those with an odd number of marks above them
    assert int(odd[1:].sum()) == sum(1 for v in range(1, N + 1) if sigma[v] % 2)

    fig, (ax, bx) = plt.subplots(2, 1, figsize=(ss.FULL, 2.9), sharex=True,
                                 gridspec_kw={"height_ratios": [1, 1.25], "hspace": 0.08})
    c = ss.SERIES
    for k in range(1, N + 1):
        col = c["exact"] if odd[k] else c["ink"]
        ax.plot([k - 1, k], [S[k - 1], S[k]], color=col, lw=1.4 if odd[k] else 1.0,
                solid_capstyle="round")
    ax.axhline(0, color=c["grid"], lw=0.5, zorder=0)
    ax.set_ylabel("position")
    ax.text(1.5, 9, r"first step $X_1=+1$", fontsize=8, color=c["ink"])
    ss.panel(ax, "a", x=0.99, y=0.06, ha="right", va="bottom")

    for k in range(2, N + 1):
        u = parent[k]
        w = k - u
        col = c["accent"] if mark[k] else (c["exact"] if (odd[k] and odd[u]) else "#D4D4D4")
        bx.add_patch(Arc(((u + k) / 2, 0), w, w * 0.9, theta1=0, theta2=180,
                         color=col, lw=1.4 if mark[k] else (0.9 if col == c["exact"] else 0.5),
                         zorder=2 if col != "#D4D4D4" else 1))
    for k in range(1, N + 1):
        bx.plot(k, 0, "o", ms=3.4, mfc=c["exact"] if odd[k] else "white",
                mec=c["exact"] if odd[k] else c["ink"], mew=0.7, zorder=3)
    top = max(k - parent[k] for k in range(2, N + 1)) * 0.45
    bx.set_ylim(-0.12 * top, top * 1.05)
    bx.set_yticks([])
    bx.set_xlim(0, N + 0.8)
    bx.set_xlabel(r"step $k$")
    v = marks[0]
    bx.annotate(f"first flip, step {v}\nits family has {len(big)} steps",
                xy=((parent[v] + v) / 2, (v - parent[v]) * 0.45), xytext=(1.0, top * 0.82),
                color=c["accent"], fontsize=8, ha="left",
                arrowprops=dict(arrowstyle="-", lw=0.5, color=c["accent"]))
    ss.panel(bx, "b", x=0.99, y=0.92, ha="right", va="top")
    for side in ("top", "right", "left"):
        bx.spines[side].set_visible(False)
    bx.tick_params(top=False, right=False, left=False)
    ss.save(fig, HERE / "family")
    print(f"marks at {marks}; first family {len(big)} steps; M_N = {int(odd[1:].sum())}")


if __name__ == "__main__":
    main()
