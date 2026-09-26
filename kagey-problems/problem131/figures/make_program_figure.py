"""The program figure shared by the four Problem 131 papers.

Run from anywhere with
    python -B make_program_figure.py

The script writes program_A, program_B, program_C and program_D as vector PDF
and 600 dpi PNG next to itself. The four files show the same figure. In
program_X the curves of Paper X are drawn in color and bold, and the curves of
the other papers are light grey, so each variant still reads in greyscale.
The figure is 6.4 in wide and has no text smaller than 8 pt at its natural size.

The four papers (all A. Pemmasani, preprint, 2026) are
  A  Uniform Bessel bounds for endpoint crossings in the persistent random walk
  B  Vertex crossings in a symmetric Markov multinomial model
  C  Face selection for slowly switching Markov chains and the planar persistent walk
  D  Endpoint crossings for random walks with memory

Panel (a) plots, against L = log N for 10 <= N <= 10^8, the value of the memory
parameter at which the middle catches up with the ends. Every model is measured
on its own switching scale. For A, B and C this is T, which is N times the
probability of switching to one given other state. For the elephant walk of D it
is x_n = n eps, and for the aging walk of D it is the expected number of
switches. Above each curve the middle beats the ends. The curves are
  A  the root z of z + (1/2) log z = L + c_0 + 1/(8z) with c_0 = (1/2) log(pi/8).
     This is the crossing equation of Paper A (the proposition on the crossing
     equation, paperA/sec_crossing.tex) with its remainder R_N dropped. There
     |R_N| <= 1/(4L^2) + (L^2 + L)/N for every N >= 2, and the root follows the
     third-order expansion of z_N = N(1 - p_N) in the corollary on the crossing
     at every N.
  B  the root z of z + (1/2) log z = L + a_k + 1/(8z) for k = 2, 3, 4, where
     a_k = (1/2) log(4 pi) - ((k + 1/2)/(k - 1)) log k. This is the crossing
     equation of the face-center crossing theorem of Paper B
     (paperB/simplex_thresholds.tex), which holds for z_{N,k} = N(1 - p_{N,k})/(d - 1)
     up to O(L^-2). check() compares it with the exact roots N u_{N,k}, which
     differ from z_{N,k} by O(L^2/N). Since a_2 = c_0, the curve for k = 2 is
     curve A, and the 3 curves nearly coincide because every face ties with the
     vertex at first order.
  C  the corner and origin crossing of the planar walk with r = s = 1, where the
     4 directions form the complete graph with unit rates. We plot the root of
     3T + log T = 2L + log(pi/16), which is the first equation of the remark
     "when turns matter" (rem:planar-turns) of Paper C with beta = 2r + s = 3
     and r + s = 2. Paper C states that remark with its proof omitted. Its slope is
     tau* = min(2/beta, 1/s) = 2/3 by the first-order theorem for the planar walk.
  D  the elephant walk, through the root g_n of x + log x = 2L - log 8. By the
     crossing theorem of Paper D, x_n = g_n + O((log n)^2/n), and by the
     comparison theorem there, x_n = 2 z_n - log(2 pi) + c_*/log n
     + O(log log n/(log n)^2) with c_* = (1/2) log(2 pi) - 1/4. On the scale
     of the figure the two forms cannot be told apart, and check() compares both
     with the exact crossings.
  D  the aging walk, which switches at step k >= 2 with probability c/k. With a
     fixed first step its crossing is exactly c = 1 for every n and every bin
     (the remark on aging in Paper D), and above it (c > 1) every
     interior bin beats the end. We plot the expected number of switches at
     c = 1, which is 1/2 + 1/3 + ... + 1/N = H_N - 1.
Panel (b) plots the heavy-tailed exponent e(alpha) = 1 - alpha + 1/alpha of
Paper D for 1 < alpha < 2. With a stationary start E_n/C_n ~ C(alpha) n^e(alpha),
so the ends win for large n exactly when alpha is below the golden ratio phi,
where e vanishes.

check() compares every plotted formula with the constants of the papers and
with the exact crossings in their data files (listed above load_exact), and
stops with a list of disagreements. If a data file is missing, for example in a
copy of the repository without paperC or paperD, check() prints a note and
skips the comparisons that need it.
"""

from __future__ import annotations

import json
import logging
from fractions import Fraction
from math import log, pi, sqrt
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
logging.getLogger("fontTools").setLevel(logging.ERROR)
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np

HERE = Path(__file__).resolve().parent
FULL = 6.4
PHI = (1 + sqrt(5)) / 2
C0 = 0.5 * log(pi / 8)
C_STAR = 0.5 * log(2 * pi) - 0.25

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

# one dark color per paper, and light grey for the papers that are not highlighted
COLOR = {"A": "#1b4f9c", "B": "#b2182b", "C": "#1b7837", "D": "#6a2c8a"}
GREY, GREY_TEXT = "0.74", "0.55"
L_MIN, L_MAX = log(10.0), log(1e8)


def save(fig, name):
    fig.savefig(HERE / f"{name}.pdf")
    fig.savefig(HERE / f"{name}.png", dpi=600)
    plt.close(fig)
    print(f"wrote {name}.pdf and {name}.png")


def panel(ax, letter, x=0.03, y=0.95):
    ax.text(x, y, f"({letter})", transform=ax.transAxes, va="top")


# ---------------------------------------------------------------- the formulas

def root_increasing(g, target, lo=1e-6, hi=200.0, iters=200):
    """Vectorized bisection for g(x) = target with g increasing in x."""
    target = np.asarray(target, dtype=float)
    lo = np.full(target.shape, lo)
    hi = np.full(target.shape, hi)
    for _ in range(iters):
        mid = (lo + hi) / 2
        above = g(mid) >= target
        hi = np.where(above, mid, hi)
        lo = np.where(above, lo, mid)
    return (lo + hi) / 2


def a_k(k):
    """The constant a_k of Paper B, with a_2 = c_0."""
    return 0.5 * log(4 * pi) - (k + 0.5) / (k - 1) * log(k)


def bessel_type(L, a):
    """Root z of z + (1/2) log z = L + a + 1/(8z) (curve A with a = c_0, curve B with a = a_k)."""
    return root_increasing(lambda z: z + 0.5 * np.log(z) - 1 / (8 * z), np.asarray(L) + a)


def planar(L, r=1.0, s=1.0):
    """Root T of beta T + log T = 2L + log(pi/(8(r + s))) (Paper C, turns dominate, s < 2r)."""
    beta = 2 * r + s
    return root_increasing(lambda t: beta * t + np.log(t), 2 * np.asarray(L) + log(pi / (8 * (r + s))))


def elephant(L):
    """Root g_n of x + log x = 2L - log 8 (Paper D)."""
    return root_increasing(lambda x: x + np.log(x), 2 * np.asarray(L) - log(8))


def aging(L):
    """Expected number of switches at c = 1 up to step N = e^L, that is H_N - 1."""
    return np.array([float(mp.harmonic(mp.e ** mp.mpf(x))) - 1 for x in np.atleast_1d(L)])


def exponent(alpha):
    """e(alpha) = 1 - alpha + 1/alpha (Paper D, 1 < alpha < 2)."""
    return 1 - alpha + 1 / alpha


def third_order(L, a):
    """L - (1/2) log L + a + ((1/4) log L - a/2 + 1/8)/L, the expansion in Papers A and B."""
    L = np.asarray(L, dtype=float)
    return L - 0.5 * np.log(L) + a + (0.25 * np.log(L) - 0.5 * a + 0.125) / L


# ---------------------------------------------------------------- checks

# The exact crossings come from the data files of the papers.
#   Paper A  N(1 - p_N) for N = 40, ..., 10240 (key "nq" of paperC/data/figdata_planar_0p1_1.json)
#            and z_n for n = 50, ..., 51200 (key "z" of paperD/data/figdata_crossing.json)
#   Paper B  a_k and the roots N u_{N,k} (paperB/data/simplex-verification.json)
#   Paper C  T*_N for (r, s) = (1, 1) and N = 40, ..., 10240 (paperC/data/figdata_planar_1_1.json)
#   Paper D  x_n for n = 50, ..., 51200 (key "x" of paperD/data/figdata_crossing.json)
# D_G and D_DIFF hold the roots g_n and the differences D(n) printed in the table of exact
# elephant crossings in Paper D.
DATA = HERE.parent
D_G = {50: 4.288636, 400: 7.843768, 1600: 10.340051, 3200: 11.610464,
       12800: 14.182921, 51200: 16.786946}
D_DIFF = {50: -0.02123, 400: -0.03319, 1600: 0.02921, 3200: 0.04786, 12800: 0.06416, 51200: 0.06522}


def load_exact():
    """The exact crossings by key, with None for a key whose data file is missing."""
    def read(path):
        file = DATA / path
        if not file.is_file():
            print(f"note: {path} is missing, so check() skips the comparisons that use it")
            return None
        return json.loads(file.read_text(encoding="utf-8"))

    rev = read("paperC/data/figdata_planar_0p1_1.json")
    turn = read("paperC/data/figdata_planar_1_1.json")
    ele = read("paperD/data/figdata_crossing.json")
    simplex = read("paperB/data/simplex-verification.json")
    simplex = None if simplex is None else simplex["threshold_checks"]
    return {
        "A": None if rev is None else {r["N"]: r["nq"] for r in rev},
        "A_z": None if ele is None else dict(zip(ele["grid"], ele["z"])),
        "B_a": None if simplex is None else {r["k"]: float(r["a_k"]) for r in simplex},
        "B": None if simplex is None else
        {k: {r["N"]: float(r["Nu_root"]) for r in simplex if r["k"] == k} for k in (2, 3, 4)},
        "C": None if turn is None else {r["N"]: r["T"] for r in turn},
        "D": None if ele is None else dict(zip(ele["grid"], ele["x"])),
    }


def aging_law(n, c):
    """Exact law of A_n for the aging walk with first step +1 and switch probability c/k at k >= 2."""
    P = {(1, 1): Fraction(1)}                   # (number of + steps, last step) -> probability
    for k in range(2, n + 1):
        q = c / k
        Q = {}
        for (a, s), w in P.items():
            for t, pr in ((s, 1 - q), (-s, q)):
                key = (a + (t == 1), t)
                Q[key] = Q.get(key, 0) + w * pr
        P = Q
    law = [Fraction(0)] * (n + 1)
    for (a, _), w in P.items():
        law[a] += w
    return law


def decreasing(xs):
    return all(abs(x) > abs(y) for x, y in zip(xs, xs[1:]))


def check():
    ex = load_exact()
    notes = []
    skipped = []

    def need(ok, msg):
        if not ok:
            notes.append(msg)

    def have(*keys, what):
        """True if the data for every key was loaded, and otherwise records the skipped comparison."""
        if all(ex[key] is not None for key in keys):
            return True
        skipped.append(what)
        return False

    def gaps(f, table):
        return [float(f(log(n))) - v for n, v in sorted(table.items())]

    # the constants
    need(abs(C0 - a_k(2)) < 1e-15, "a_2 should equal c_0 = (1/2) log(pi/8)")
    if have("B_a", what="a_k against Paper B's data"):
        for k in (2, 3, 4):
            need(abs(a_k(k) - ex["B_a"][k]) < 1e-14, f"a_{k}, Paper B {ex['B_a'][k]}, formula {a_k(k)}")
    need(a_k(2) > a_k(3) > a_k(4), "Paper B has a_2 > a_3 > a_4")
    need(abs(C_STAR - 0.668939) < 5e-7, "c_* = 0.668939... in Paper D")

    # the A and B curves solve their equations and follow the third-order expansion
    Ls = np.linspace(L_MIN, L_MAX, 50)
    for a in (C0, a_k(3), a_k(4)):
        z = bessel_type(Ls, a)
        need(np.allclose(z + 0.5 * np.log(z) - 1 / (8 * z), Ls + a, atol=1e-12), "root of the A/B equation")
        gap = np.abs(z - third_order(Ls, a))
        need(np.all(gap <= (np.log(Ls) / Ls) ** 2), "A/B root is not within (log L/L)^2 of the expansion")

    # curve A against the exact crossings of Paper A
    for key in ("A", "A_z"):
        if have(key, what=f"curve A against the exact crossings ({key})"):
            d = gaps(lambda L: bessel_type(L, C0), ex[key])
            need(decreasing(d) and 0 < d[0] < 0.06 and abs(d[-1]) < 2e-3, f"curve A against Paper A ({key}), {d}")

    # curve B against the exact roots N u_{N,k} of Paper B
    if have("B", what="curve B against the exact roots of Paper B"):
        for k in (2, 3, 4):
            d = gaps(lambda L: bessel_type(L, a_k(k)), ex["B"][k])
            need(decreasing(d) and abs(d[0]) < 0.35 and abs(d[-1]) < 1e-3, f"curve B, k = {k}, against Paper B, {d}")

    # curve C, the first-order slope, the equivalent form and the exact crossings of Paper C
    r, s = 1.0, 1.0
    beta = 2 * r + s
    need(s < 2 * r and abs(min(2 / beta, 1 / s) - 2 / 3) < 1e-15, "r = s = 1 should give tau* = 2/3 with turns dominating")
    if have("C", what="curve C against the exact crossings of Paper C"):
        d = gaps(planar, ex["C"])
        need(decreasing(d) and 0 < d[0] < 0.25 and d[-1] < 0.05, f"curve C against Paper C, {d}")
    other = (2 * bessel_type(Ls, C0) + log(beta / (2 * (r + s)))) / beta   # beta T = 2 z_N + log(beta/(2(r + s)))
    need(np.all(np.abs(other - planar(Ls)) < 0.02), "the 2 forms of the planar crossing disagree")
    need(0.55 < float(planar(L_MAX)) / L_MAX < 2 / 3, "T*/L at N = 10^8 should be a little below 2/3")

    # curve D, elephant. g_n reproduces Paper D's table and lies above x_n, with a shrinking gap
    for n, g in D_G.items():
        need(abs(float(elephant(log(n))) - g) < 1e-6, f"g_n at n = {n}")
    if have("D", what="curve D against the exact elephant crossings of Paper D"):
        d = gaps(elephant, ex["D"])
        need(all(v > 0 for v in d) and decreasing(d) and d[0] < 0.35 and d[-1] < 0.01, f"g_n - x_n, {d}")
    if have("D", "A_z", what="the differences D(n) of Paper D"):
        for n, v in D_DIFF.items():           # D(n) = x_n - (2 z_n - log(2 pi)) with the exact z_n
            got = ex["D"][n] - (2 * ex["A_z"][n] - log(2 * pi))
            need(abs(got - v) < 1e-5, f"D({n}), Paper D {v}, data {got}")
    # the comparison theorem of Paper D, x_n - (2 z_n - log(2 pi)) = c_*/L + O(log L/L^2)
    gap = elephant(Ls) - (2 * bessel_type(Ls, C0) - log(2 * pi))
    need(np.all(np.abs(gap - C_STAR / Ls) <= 2 * (np.log(Ls) / Ls) ** 2),
         "the 2 forms of the elephant crossing do not differ by c_*/L")

    # curve D, aging. At c = 1 with a fixed first step, A_n is uniform on {1, ..., n}
    for n in range(2, 15):
        law = aging_law(n, Fraction(1))
        need(law[0] == 0 and all(p == Fraction(1, n) for p in law[1:]), f"aging law at c = 1, n = {n}")
    for c, sign in ((Fraction(9, 10), -1), (Fraction(11, 10), 1)):
        law = aging_law(14, c)
        need(all((law[j] - law[14]) * sign > 0 for j in range(1, 14)), f"aging at c = {c}")
    need(abs(float(aging(log(1000.0))[0]) - (float(mp.harmonic(1000)) - 1)) < 1e-12, "H_N - 1 at N = 1000")

    # panel (b), the exponent and the golden ratio
    need(abs(exponent(PHI)) < 1e-15 and exponent(1.0) == 1 and exponent(2.0) == -0.5, "e(alpha) values")
    al = np.linspace(1.001, 1.999, 999)
    e = exponent(al)
    need(np.all(np.diff(e) < 0) and np.all((e > 0) == (al < PHI)), "e(alpha) changes sign only at phi")
    need(abs(exponent(5 / 3) + 1 / 15) < 1e-15, "e(5/3) = -1/15")

    if notes:
        raise SystemExit("disagreements with the papers\n  " + "\n  ".join(notes))
    if skipped:
        print(f"check: skipped {len(skipped)} comparisons whose data file is missing: " + "; ".join(skipped))
        print("check: every other plotted formula agrees with the papers")
    else:
        print("check: every plotted formula agrees with the papers")


# ---------------------------------------------------------------- the figure

def curves():
    L = np.linspace(L_MIN, L_MAX, 500)
    return L, {
        ("A", "A"): bessel_type(L, C0),
        ("B", 2): bessel_type(L, a_k(2)),
        ("B", 3): bessel_type(L, a_k(3)),
        ("B", 4): bessel_type(L, a_k(4)),
        ("C", "C"): planar(L),
        ("D", "elephant"): elephant(L),
        ("D", "aging"): aging(L),
    }


STYLE = {("A", "A"): "-", ("B", 2): "-", ("B", 3): (0, (4, 1.6)), ("B", 4): (0, (1, 1.2)),
         ("C", "C"): "-", ("D", "elephant"): "-", ("D", "aging"): (0, (5, 1.5, 1, 1.5))}
# (paper, curve, label, height of the label at the right edge, None meaning the end of the curve)
LABELS = [("D", "elephant", "D  elephant", None),
          ("D", "aging", "D  aging", 19.8),
          ("A", "A", r"A  $z_N$", 17.2),
          ("B", 3, r"B  $k=2,3,4$", 14.6),
          ("C", "C", "C  planar", None)]
YMAX = 34.0


def fig_program(L, ys, hi):
    fig = plt.figure(figsize=(FULL, 2.7))
    ax = fig.add_axes([0.062, 0.135, 0.505, 0.745])
    bx = fig.add_axes([0.782, 0.135, 0.213, 0.745])

    # panel (a), with the grey curves first and the highlighted paper on top
    for key, y in sorted(ys.items(), key=lambda kv: kv[0][0] == hi):
        on = key[0] == hi
        bold = 1.25 if key[0] == "B" else 1.7      # the 3 curves of B lie within 0.4 of each other
        ax.plot(L, y, ls=STYLE[key], color=COLOR[key[0]] if on else GREY,
                lw=bold if on else 0.9, zorder=3 if on else 2)
    for paper, which, text, y_lab in LABELS:
        on = paper == hi
        y_end = float(ys[(paper, which)][-1])
        ax.annotate(text, xy=(L_MAX, y_end), xytext=(L_MAX + 0.5, y_end if y_lab is None else y_lab),
                    va="center", ha="left", annotation_clip=False,
                    color=COLOR[paper] if on else GREY_TEXT, fontweight="bold" if on else "normal",
                    arrowprops=dict(arrowstyle="-", lw=0.5, color=COLOR[paper] if on else GREY,
                                    shrinkA=1, shrinkB=0.5))
    ax.set_xlim(L_MIN, L_MAX)
    ax.set_ylim(0, YMAX)
    ax.set_xlabel(r"$L=\log N$")
    ax.set_ylabel(r"$T$ at the crossing")
    ax.tick_params(top=False)
    top = ax.twiny()
    top.set_xlim(L_MIN, L_MAX)
    top.set_xticks([log(10.0 ** j) for j in range(1, 9)])
    top.set_xticklabels([rf"$10^{j}$" for j in range(1, 9)])
    top.tick_params(direction="in", length=3, pad=1.5)
    top.set_xlabel(r"$N$", labelpad=2)
    panel(ax, "a", x=0.03, y=0.965)

    # the 2 phases, each placed where it holds for every curve
    lo_curve = min(float(y[L >= 12.5].min()) for y in ys.values())
    hi_curve = max(float(y[L <= 9.5].max()) for y in ys.values())
    assert hi_curve < 0.62 * YMAX and lo_curve > 0.2 * YMAX, "a phase label would overlap a curve"
    ax.text(0.03, 0.855, "above each curve\nthe middle beats the ends", transform=ax.transAxes,
            va="top", ha="left", color="0.2", linespacing=1.3)
    ax.text(0.975, 0.022, "below each curve\nthe ends beat the middle", transform=ax.transAxes,
            va="bottom", ha="right", color="0.2", linespacing=1.3)

    # panel (b), the heavy-tailed exponent of Paper D
    on = hi == "D"
    col = COLOR["D"] if on else GREY
    al = np.linspace(1.0, 2.0, 400)
    bx.axhline(0.0, color="0.55", lw=0.5, ls=":")
    bx.plot([PHI, PHI], [-0.6, 0.0], color="0.55", lw=0.5, ls=":")
    bx.plot(al, exponent(al), color=col, lw=1.7 if on else 0.9, zorder=3)
    bx.plot([PHI], [0.0], "o", ms=3.5, mfc="white", mec=col, mew=1.0, zorder=4)
    bx.set_xlim(1.0, 2.0)
    bx.set_ylim(-0.6, 1.4)
    bx.set_yticks([-0.5, 0.0, 0.5, 1.0])
    bx.set_yticklabels(["$-0.5$", "0", "0.5", "1"])
    bx.set_xticks([1.0, PHI, 2.0])
    bx.set_xticklabels(["1", r"$\varphi$", "2"])
    bx.set_xticks([1.25, 1.5, 1.75], minor=True)
    bx.set_xlabel(r"run exponent $\alpha$")
    bx.set_ylabel(r"$e(\alpha)=1-\alpha+1/\alpha$", labelpad=1)
    bx.set_title("D  heavy-tailed runs", fontsize=8, pad=4, color=col if on else GREY_TEXT,
                 fontweight="bold" if on else "normal")
    # The sign of e(alpha) decides the winner: e > 0 (alpha < phi) means the ends win.
    bx.text(0.975, 0.965, "$\\alpha>\\varphi$: middle\nbeats the ends", transform=bx.transAxes,
            ha="right", va="top", color="0.2", linespacing=1.3)
    bx.text(0.05, 0.04, "$\\alpha<\\varphi$: ends\nbeat the middle", transform=bx.transAxes,
            ha="left", va="bottom", color="0.2", linespacing=1.3)
    panel(bx, "b", x=0.05, y=0.965)
    box = fig.get_tightbbox(fig.canvas.get_renderer())
    assert abs(box.width - FULL) < 0.08, f"the saved figure would be {box.width:.2f} in wide"
    save(fig, f"program_{hi}")


if __name__ == "__main__":
    check()
    L, ys = curves()
    for paper in "ABCD":
        fig_program(L, ys, paper)
