"""Analytic second-order envelope on the complete graph for Paper C1; no simulation or DP.

Run from anywhere: python -B make_complete_envelope.py
Writes fig_complete_envelope.pdf, .png, and .json beside this script only.

Sources in ../sec_complete.tex:
  cor:paperB, thm:simplex-crossing(ii): log D_k and the limiting scores;
  cor:simplex-modes: the single jump from one state to all d.
All lines are limiting log face maxima relative to V_N, at
T = log N - (1/2) log log N + t, with d=4 and the uniform start.
No finite-N probabilities or finite-N tie locations are plotted.

Until October 24, 2026 the figure had a second panel with a weak field. That
material was cut from the paper, and the panel with it.
"""

from __future__ import annotations

import json
from itertools import combinations
from math import log, pi
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Rectangle
import numpy as np


HERE = Path(__file__).resolve().parent
STEM = "fig_complete_envelope"
D = 4
# 280 PDF points wide, included at 0.62 of the text width.
SIZE = (280 / 72, 3.3)
COLORS = ("#222222", "#0072B2", "#D55E00", "#7A5195")
STYLES = ("-", (0, (5, 2.5)), (0, (1, 1.8)), (0, (5, 2, 1, 2)))
RC = {
    "font.family": "DejaVu Serif", "font.size": 8.5,
    "mathtext.fontset": "dejavuserif", "axes.labelsize": 8.5,
    "axes.titlesize": 9, "xtick.labelsize": 8.5, "ytick.labelsize": 8.5,
    "axes.linewidth": 0.65, "axes.spines.top": False,
    "axes.spines.right": False, "xtick.direction": "out",
    "ytick.direction": "out", "pdf.fonttype": 42, "ps.fonttype": 42,
    "text.usetex": False, "savefig.facecolor": "white",
}


def log_d(k):
    """log(k**(k+1/2) / (4*pi)**((k-1)/2)), including D_1=1."""
    return (k + 0.5) * log(k) - 0.5 * (k - 1) * log(4 * pi)


def scores(t, intercepts):
    return np.asarray(t)[..., None] * np.arange(D) + intercepts


def envelope_segments(intercepts, limits):
    """Find every upper-envelope segment using all pairwise intersections.

    This uses affine geometry, not a sampled approximation to a kink. Segments
    crossing irrelevant intersections are merged before drawing the envelope.
    """
    lo, hi = limits
    knots = {lo, hi}
    for i, j in combinations(range(D), 2):
        t = (intercepts[i] - intercepts[j]) / (j - i)
        if lo < t < hi:
            knots.add(float(t))
    knots = sorted(knots)
    segments = []
    for left, right in zip(knots, knots[1:]):
        k = int(np.argmax(scores((left + right) / 2, intercepts))) + 1
        if segments and segments[-1][2] == k:
            segments[-1] = (segments[-1][0], right, k)
        else:
            segments.append((left, right, k))
    return segments


def verify(c, segments):
    """Check the plotted claims against independent forms of the formulas."""
    a = np.array([-c[k - 1] / (k - 1) for k in range(2, D + 1)])
    a_formula = np.array([
        0.5 * log(4 * pi) - (k + 0.5) / (k - 1) * log(k)
        for k in range(2, D + 1)
    ])
    assert np.allclose(a, a_formula, rtol=0, atol=1e-14)
    assert np.all(np.diff(a) < 0)
    assert [s[2] for s in segments] == [1, D]
    assert abs(segments[0][1] - a[-1]) < 1e-14
    probes = []
    for left, right, winner in segments:
        t = (left + right) / 2
        values = scores(t, c)
        gap = float(values[winner - 1] - np.max(np.delete(values, winner - 1)))
        assert gap > 0
        # Enumerate all 15 supports, independently of the reduction to sizes.
        all_support_scores = []
        for k in range(1, D + 1):
            for subset in combinations(range(D), k):
                all_support_scores.append(((k - 1) * t + log_d(k), subset))
        assert abs(max(s[0] for s in all_support_scores) - values[winner - 1]) < 1e-13
        probes.append({"t": t, "winning_k": winner, "score_gap_to_next_size": gap})
    return {
        "dimension": D,
        "coordinate": "T = log N - (1/2) log log N + t",
        "claim_scope": "limiting log face maxima relative to V_N; not finite-N ties",
        "log_D_k": c.tolist(), "a_2_through_a_d": a.tolist(),
        "transition": float(a[-1]),
        "intermediate_scores_at_a_d": scores(a[-1], c)[1:-1].tolist(),
        "visible_envelope_segments": segments, "interior_checks": probes,
        "source_labels": ["cor:paperB", "thm:simplex-crossing", "cor:simplex-modes"],
        "checks": "constants agree with a_k; all 15 supports checked at each phase probe; "
                  "the envelope jumps from size 1 to size 4 at a_4",
        "output_size_inches": list(SIZE), "minimum_label_size_pt": 8.5,
    }


def main():
    c = np.array([log_d(k) for k in range(1, D + 1)])
    lim = (-1.15, -0.25)
    segments = envelope_segments(c, lim)
    evidence = verify(c, segments)

    with plt.rc_context(RC):
        fig, ax = plt.subplots(figsize=SIZE)
        fig.subplots_adjust(left=0.15, right=0.97, bottom=0.34, top=0.82)
        # The candidate scores are exactly straight lines.
        for k, (color, style) in enumerate(zip(COLORS, STYLES), start=1):
            ax.plot(lim, scores(lim, c)[:, k - 1], color=color, ls=style, lw=0.95, zorder=2)
        for left, right, k in segments:
            xx = np.array([left, right])
            ax.plot(xx, scores(xx, c)[:, k - 1], color="black", lw=2.15,
                    solid_capstyle="butt", zorder=3)
        for _, t, k in segments[:-1]:
            value = float(scores(t, c)[k - 1])
            ax.plot([t, t], [-1.2, value], color="0.5", lw=0.65, ls=(0, (2, 2.5)), zorder=0)
            ax.plot(t, value, "o", mfc="white", mec="black", ms=3.4, mew=0.85, zorder=4)
            ax.annotate(r"$a_4$", (t, value), xytext=(-4, 7),
                        textcoords="offset points", ha="right", va="bottom")
        ax.set(xlim=lim, ylim=(-1.2, 2.25), yticks=[-1, 0, 1, 2], xlabel=r"$t$")
        ax.set_xticks([-1.1, -0.9, -0.7, -0.5, -0.3])
        ax.tick_params(length=3, width=0.65, pad=3)
        ax.axhline(0, color="0.88", lw=0.5, zorder=0)
        ax.set_ylabel(r"Limiting log score $\ell_k(t)$", labelpad=6)
        # Separate strip makes the answer readable without distinguishing colors.
        strip = ax.inset_axes([0, -0.43, 1, 0.12])
        strip.set(xlim=lim, ylim=(0, 1))
        strip.set_axis_off()
        for left, right, k in segments:
            strip.add_patch(Rectangle((left, 0), right - left, 1,
                                      facecolor="0.96", edgecolor="0.25", lw=0.65))
            strip.text((left + right) / 2, 0.5, str(k), ha="center", va="center")
        handles = [Line2D([], [], color=co, ls=ls, lw=1, label=rf"$k={k}$")
                   for k, (co, ls) in enumerate(zip(COLORS, STYLES), start=1)]
        handles.append(Line2D([], [], color="black", lw=2.15, label="envelope"))
        fig.legend(handles=handles, loc="upper center", bbox_to_anchor=(0.55, 0.992),
                   ncol=3, frameon=False, handlelength=2.1, columnspacing=0.95,
                   handletextpad=0.5, fontsize=8.5)
        fig.text(0.56, 0.078, r"Winning support size $k$", ha="center")
        fig.text(0.56, 0.022, r"$K_4$, uniform start, $T=\log N-\frac{1}{2}\log\log N+t$",
                 ha="center")
        metadata = {
            "Title": "Complete graph: support selection without a field",
            "Subject": "Limiting second-order face scores, not finite-N ties; Paper C1",
            "Creator": "make_complete_envelope.py (Matplotlib)",
            "CreationDate": None, "ModDate": None,
        }
        # Fixed MediaBox and embedded TrueType fonts; no rasterized artists.
        fig.savefig(HERE / f"{STEM}.pdf", metadata=metadata)
        fig.savefig(HERE / f"{STEM}.png", dpi=400)
        plt.close(fig)
    (HERE / f"{STEM}.json").write_text(json.dumps(evidence, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {STEM}.pdf/.png/.json; analytic checks passed.")
    print(f"Jump from one state to all four at a_4 = {evidence['transition']:.10f}")


if __name__ == "__main__":
    main()
