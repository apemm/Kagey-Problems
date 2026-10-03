"""Make the figures of problem137_general.tex.

  figures/fig_tree_m1.tex, figures/fig_tree_m2.tex   TikZ trees of ranks 0..7 for m = 1 and m = 2
  figures/growth.pdf                                 a_q(n) / psi_q^n for q = 3, 4, 5, 6 and the free case

The trees are computed by BFS in exact rationals, with the parent of each point being the point that
first reaches it (by Corollary 5 this is P(x)). Usage: python make_figures.py
"""
import os
from fractions import Fraction as Fr

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "figures")
DEPTH = 7


def tree(m, depth):
    g = lambda x: Fr(-1) / (m * x)
    rank = {Fr(0): 0}
    kids = {Fr(0): []}
    layer = [Fr(0)]
    for n in range(1, depth + 1):
        nxt = []
        for x in layer:
            cand = ([(g(x), 'g')] if x != 0 else []) + [(x + 1, 'f')]   # g-child drawn on the left
            for y, mv in cand:
                if y not in rank:
                    rank[y] = n
                    kids[y] = []
                    kids[x].append((y, mv))
                    nxt.append(y)
        layer = nxt
    return rank, kids


def layout(kids, root):
    pos = {}
    slot = [0]

    def walk(x):
        ch = kids[x]
        if not ch:
            pos[x] = slot[0]
            slot[0] += 1
        else:
            for y, _ in ch:
                walk(y)
            pos[x] = (pos[ch[0][0]] + pos[ch[-1][0]]) / 2
    walk(root)
    return pos, slot[0]


def name(x):
    s = 'm' if x < 0 else ''
    return f"n{s}{abs(x.numerator)}_{x.denominator}"


def label(x):
    if x.denominator == 1:
        return f"${x.numerator}$"
    sgn = '-' if x < 0 else ''
    return f"${sgn}\\tfrac{{{abs(x.numerator)}}}{{{x.denominator}}}$"


def tikz(m, path, width_cm=15.0, dy=1.05):
    rank, kids = tree(m, DEPTH)
    pos, nslots = layout(kids, Fr(0))
    dx = width_cm / max(nslots - 1, 1)
    L = ["\\begin{tikzpicture}[every node/.style={font=\\scriptsize}]"]
    for x in sorted(rank, key=lambda z: (rank[z], pos[z])):
        sty = 'vroot' if x == 0 else ('vpos' if x > 0 else 'vneg')
        L.append(f"\\node[{sty}] ({name(x)}) at ({pos[x] * dx:.2f},{-rank[x] * dy:.2f}) {{{label(x)}}};")
    L.append(f"\\node[rk] at (-0.6,{0.6 * dy:.2f}) {{rank}};")
    for n in range(DEPTH + 1):
        L.append(f"\\node[rk] at (-0.6,{-n * dy:.2f}) {{{n}}};")
    for x in sorted(rank, key=lambda z: (rank[z], pos[z])):
        for y, mv in kids[x]:
            L.append(f"\\draw[e{mv}] ({name(x)}) -- ({name(y)});")
    # f applied to a leaf x < -1 gives x + 1, which is 2q - 3 ranks older
    for x in rank:
        if x < -1 and (x + 1) in rank:
            L.append(f"\\draw[eold] ({name(x)}) -- ({name(x + 1)});")
    L.append("\\end{tikzpicture}")
    with open(path, 'w') as fh:
        fh.write("\n".join(L) + "\n")
    print(f"m = {m}: {len(rank)} vertices, {nslots} leaf slots -> {path}")


def series(q, n):
    if q is None:
        num, den = [1], [1, -1, -1]
    else:
        den = [0] * (2 * q - 2)
        den[0], den[1] = 1, -1
        for j in range(3, 2 * q - 2, 2):
            den[j] = -1
        num = [0] * (2 * q - 2)
        for j in range(0, 2 * q - 3, 2):
            num[j] = 1
        num[2 * q - 3] = -1
    a = []
    for k in range(n + 1):
        s = num[k] if k < len(num) else 0
        s -= sum(den[j] * a[k - j] for j in range(1, len(den)) if k - j >= 0)
        a.append(s)
    return a


def growth(path):
    # psi_q from verify_general.py (40-digit root finding)
    psi = {3: 1.46557123188, 4: 1.57014731220, 5: 1.60134733379, 6: 1.61193039656,
           None: 1.61803398875}
    colors = ["#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4"]
    marks = ["o", "s", "^", "D", "v"]
    names = {3: r"$q=3$ ($m=1$)", 4: r"$q=4$ ($m=2$)", 5: r"$q=5$", 6: r"$q=6$ ($m=3$)",
             None: r"$q=\infty$ ($m\geq4$)"}
    N = 40
    plt.rcParams.update({"font.size": 9, "font.family": "serif", "mathtext.fontset": "cm"})
    fig, ax = plt.subplots(figsize=(5.6, 2.9))
    for i, q in enumerate([3, 4, 5, 6, None]):
        a = series(q, N)
        ys = [a[n] / psi[q] ** n for n in range(N + 1)]
        ax.plot(range(N + 1), ys, color=colors[i], marker=marks[i], markersize=3.2, linewidth=1.0,
                label=names[q])
    ax.set_xlabel(r"rank $n$")
    ax.set_ylabel(r"$a(n)\,/\,\psi_q^{\,n}$")
    ax.set_xlim(0, N)
    ax.set_ylim(0.55, 1.05)
    ax.grid(True, color="#e4e3df", linewidth=0.6)
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)
    for s in ("left", "bottom"):
        ax.spines[s].set_color("#8a8984")
    ax.legend(frameon=False, ncol=3, loc="upper right", fontsize=8)
    fig.tight_layout()
    fig.savefig(path)
    print(f"growth plot -> {path}")


if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    tikz(1, os.path.join(OUT, "fig_tree_m1.tex"))
    tikz(2, os.path.join(OUT, "fig_tree_m2.tex"))
    growth(os.path.join(OUT, "growth.pdf"))
