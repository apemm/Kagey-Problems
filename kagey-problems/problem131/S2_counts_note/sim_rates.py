"""How fast can the net flow and the entropy production be learned from counts?

Three states, a stationary start, and the N-step chain with transition matrix
I + (T/N) Q, whose count vector has an exact law (dynamic program). The two-way
flows c and the stationary law pi are known. The only unknown is the flow j
around the triangle, with J_12 = J_23 = J_31 = j. The law is even in j, so we
estimate |j| by maximum likelihood on j >= 0.

1. The chi-square distance between the laws at j = delta and j = 0 is of
   order delta^4 (Theorem `thm:lecam`).
2. Root mean squared errors over repeated samples of n count vectors:
   at j = 0 the error of |j| falls like n^(-1/4) and the error of the entropy
   production like n^(-1/2); at j = 0.1 the error of |j| falls like n^(-1/2).
Writes fig_rates.pdf and prints the fitted slopes.

Run:  python -B sim_rates.py     (about a minute)
"""
import sys
from math import log
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "figures"))
sys.path.insert(0, str(HERE))
import dark_style as ds
import check_information as ci

PI = np.array([0.5, 0.3, 0.2])
C = {(0, 1): 0.30, (0, 2): 0.20, (1, 2): 0.25}
T, N = 2.0, 40
JMAX, GRID = 0.15, 601
NS = [10 ** 2, 10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6]
REPS = 400

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


def theta_of(j):
    """Rates Q_ij = f_ij / pi_i with f_ij = (c_ij + J_ij)/2, in the order of ci.OFFS."""
    J = {(0, 1): j, (1, 2): j, (2, 0): j, (1, 0): -j, (2, 1): -j, (0, 2): -j}
    out = []
    for (a, b) in ci.OFFS:
        c = C[(min(a, b), max(a, b))]
        out.append(0.5 * (c + J[(a, b)]) / PI[a])
    return np.array(out)


def sigma_of(j):
    j = np.asarray(j, dtype=float)
    out = np.zeros_like(j)
    for c in C.values():
        out = out + np.where(j > 0, j * np.log((c + j) / (c - j)), 0.0)
    return out


def law(j):
    p = ci.count_law(theta_of(j), T, N, "stationary").real
    return np.array([p[a, b] for a in range(N + 1) for b in range(N + 1 - a)])


def main():
    rng = np.random.default_rng(2026)
    js = np.linspace(0.0, JMAX, GRID)
    table = np.array([law(j) for j in js])
    assert np.allclose(table.sum(1), 1.0)
    assert abs(table[0] - law(-0.0)).max() < 1e-15
    # the stationary law of Q really is PI, and the law is even in j
    assert abs(ci.stat(ci.build_Q(theta_of(0.07))).real - PI).max() < 1e-12
    assert abs(law(0.07) - law(-0.07)).max() < 1e-13
    logt = np.log(table)

    print("1. chi-square distance from the reversible chain")
    for d1, d2 in ((0.02, 0.04), (0.04, 0.08)):
        x1 = ((law(d1) - table[0]) ** 2 / table[0]).sum()
        x2 = ((law(d2) - table[0]) ** 2 / table[0]).sum()
        print("   chi2(%.2f) = %.3e, chi2(%.2f) = %.3e, ratio %.2f (2^4 = 16)" % (d1, x1, d2, x2, x2 / x1))

    def mle(counts):
        ll = logt @ counts
        k = int(np.argmax(ll))
        if 0 < k < GRID - 1:                         # refine with a parabola
            a, b, c = ll[k - 1], ll[k], ll[k + 1]
            den = a - 2 * b + c
            shift = 0.5 * (a - c) / den if den < 0 else 0.0
            return js[k] + shift * (js[1] - js[0])
        return js[k]

    res = {}
    for name, jtrue in (("zero", 0.0), ("away", 0.1)):
        p = law(jtrue)
        rows = []
        for n in NS:
            est = np.array([mle(rng.multinomial(n, p)) for _ in range(REPS)])
            rows.append((np.sqrt(np.mean((est - jtrue) ** 2)),
                         np.sqrt(np.mean((sigma_of(est) - sigma_of(np.array(jtrue))) ** 2))))
        res[name] = np.array(rows)

    def slope(y):
        return np.polyfit(np.log(NS[1:]), np.log(y[1:]), 1)[0]

    print("2. root mean squared errors, %d samples each" % REPS)
    print("   n          :", NS)
    print("   j = 0, |j| :", np.round(res["zero"][:, 0], 5), " slope %.3f (expect -1/4)" % slope(res["zero"][:, 0]))
    print("   j = 0, sig :", np.round(res["zero"][:, 1], 6), " slope %.3f (expect -1/2)" % slope(res["zero"][:, 1]))
    print("   j = .1, |j|:", np.round(res["away"][:, 0], 5), " slope %.3f (expect -1/2)" % slope(res["away"][:, 0]))

    fig, ax = plt.subplots(figsize=(3.6, 2.6))
    ns = np.array(NS, dtype=float)
    ax.plot(ns, res["zero"][:, 0], "o-", color=ds.YELLOW, ms=3.5, label=r"$|\hat\jmath|$ at $j=0$")
    ax.plot(ns, res["away"][:, 0], "s-", color=ds.BLUE, ms=3.2, label=r"$|\hat\jmath|$ at $j=0.1$")
    ax.plot(ns, res["zero"][:, 1], "^-", color=ds.RED, ms=3.5, label=r"$\hat\sigma$ at $j=0$")
    for expo, anchor in ((-0.25, res["zero"][2, 0]), (-0.5, res["away"][2, 0]), (-0.5, res["zero"][2, 1])):
        ax.plot(ns, anchor * (ns / ns[2]) ** expo, ":", color="0.45", lw=0.9)
    ax.text(ns[-1], res["zero"][-1, 0] * 1.35, r"$n^{-1/4}$", ha="right", va="bottom")
    ax.text(ns[-1], res["away"][-1, 0] * 1.35, r"$n^{-1/2}$", ha="right", va="bottom")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel(r"number $n$ of count vectors")
    ax.set_ylabel("root mean squared error")
    ax.legend(frameon=False, loc="lower left")
    ds.finish(fig)
    fig.savefig(HERE / "fig_rates.pdf")
    fig.savefig(HERE / "fig_rates.png", dpi=400)
    print("wrote fig_rates")


if __name__ == "__main__":
    main()
