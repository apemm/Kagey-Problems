"""The figure of Paper F: the four pieces of the row at N = 5000, and the antimode against N.

Reads data/atlas_N5000.json (certify_atlas.py) and data/antimode.json (certify_antimode.py),
writes figures/atlas.pdf and .png, and records the zones and the maximal relative error of each
piece in its zone in data/atlas_pieces.json.

Run from anywhere:  py -I figures/make_atlas_figure.py
"""
import hashlib
import importlib.util
import json
from datetime import date
from pathlib import Path

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from scipy.integrate import quad
from scipy.special import gamma

HERE = Path(__file__).resolve().parent
PAPER = HERE.parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


style = load("series_style", PAPER.parent / "figures" / "series_style.py")
ca = load("certify_atlas", PAPER / "certify_atlas.py")


def stable_profile(alpha, theta_plus=1.0, theta_minus=1.0, p=0.5):
    """h_N for equal indices: the density of (1-p) theta_+ Z_+ - p theta_- Z_-, by inversion of
    its characteristic function exp(K[(-i(1-p)theta_+ t)^alpha + (i p theta_- t)^alpha]).
    For p = 1/2 and theta_+ = theta_- the law is symmetric and the inversion is a cosine transform."""
    K = -gamma(1 - alpha)
    c = 2 * K * abs(np.cos(np.pi * alpha / 2)) * ((1 - p) * theta_plus) ** alpha
    assert theta_plus * (1 - p) == theta_minus * p

    def h(x):
        val, _ = quad(lambda t: np.exp(-c * t ** alpha), 0, 60, weight="cos", wvar=abs(x), limit=400)
        return val / np.pi
    return h


def main():
    d = json.loads((PAPER / "data" / "atlas_N5000.json").read_text())
    am = json.loads((PAPER / "data" / "antimode.json").read_text())
    P = np.array(d["P"])
    N, mu, s, alpha = d["N"], d["mu"], d["s"], d["alpha"]
    f, T = ca.law_arrays(N + 1)
    u, _ = ca.renewal(f, N)
    k = np.arange(N + 1)
    y = k - 0.5 * N                                     # k - pN

    # scales: a(t) with t T(a(t)) -> 1, T(n) ~ n^-alpha/(alpha zeta(alpha+1)); B_N = a(N/s)
    from flint import arb
    zeta_a1 = float((arb(alpha) + 1).zeta().mid())
    B = ((N / s) / (alpha * zeta_a1)) ** (1 / alpha)

    # the four pieces
    h = stable_profile(alpha)
    bulk = np.array([h(t / B) for t in y]) / B
    L = np.abs(2 * k - N)                               # L_k = |k - pN| / (1 - p)
    big_plus = (N - L) / mu * f[L] + T[L] * u[N - k]                         # k > pN, kappa_+ = u_-
    big_minus = (N - L) / mu * f[L] + T[L] * u[k] * (k >= 1)                 # k < pN, kappa_- = u_+ 1{k>=1}
    big = np.where(k >= N / 2, big_plus, big_minus)
    layer_plus = T[N] * u[N - k]
    layer_minus = T[N] * u[k] * (k >= 1)
    layer = np.where(k >= N / 2, layer_plus, layer_minus)

    # zones, in units of B_N; each junction band has width B_N
    Kb, Kj, Jl = 3, 4, 1                                # bulk |y|<=3B, big jump |y|>=4B and j>=2B, layer j<=B
    dist_end = np.minimum(k, N - k)
    z_bulk = np.abs(y) <= Kb * B
    z_big = (np.abs(y) >= Kj * B) & (dist_end >= (Jl + 1) * B)
    z_layer = (dist_end <= Jl * B) & (k >= 1) & (k <= N - 1)

    def maxrel(q, z):
        z = z & (P > 0)
        r = np.abs(q[z] / P[z] - 1)
        i = int(np.argmax(r))
        return float(r[i]), int(k[z][i])
    errs = {
        "bulk": maxrel(bulk, z_bulk),
        "big_jump": maxrel(big, z_big),
        "boundary_layer": maxrel(layer, z_layer),
        "atom_plus": float(abs(P[N] / T[N] - 1)),
    }
    (PAPER / "data" / "atlas_pieces.json").write_text(json.dumps({
        "header": {"script": "figures/make_atlas_figure.py",
                   "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   "date": date.today().isoformat(), "input": "data/atlas_N5000.json"},
        "N": N, "B_N": B,
        "zones": {"bulk": f"|k-pN| <= {Kb} B_N", "big_jump": f"|k-pN| >= {Kj} B_N and min(k,N-k) >= {Jl + 1} B_N",
                  "boundary_layer": f"1 <= min(k,N-k) <= {Jl} B_N", "atom": "k = N (P_N(0) = 0 for a fresh plus start)"},
        "max_relative_error_and_bin": errs,
        "center": {"P_N(pN)": float(P[N // 2]), "bulk_profile(pN)": float(bulk[N // 2])},
    }, indent=1))
    print("zone errors:", errs, "B_N =", B)

    # ------------------------------------------------------------------ figure
    style.use()
    S = style.SERIES
    c_bulk, c_big, c_layer = style.shades(3, 0.0, 1.0)
    fig = plt.figure(figsize=(style.FULL, 2.55))
    gs = fig.add_gridspec(1, 2, width_ratios=[2.05, 1.0], wspace=0.28)
    ax = fig.add_subplot(gs[0])
    bx = fig.add_subplot(gs[1])

    # left panel: a piecewise linear horizontal scale that stretches the last W bins at each end
    W = 250
    frac = 0.17                                         # share of the axis for each end stretch

    def fwd(x):
        x = np.asarray(x, dtype=float)
        mid = (1 - 2 * frac) / (N - 2 * W)
        return np.where(x < W, frac * x / W,
                        np.where(x > N - W, 1 - frac * (N - x) / W, frac + (x - W) * mid))

    def inv(t):
        t = np.asarray(t, dtype=float)
        mid = (1 - 2 * frac) / (N - 2 * W)
        return np.where(t < frac, W * t / frac,
                        np.where(t > 1 - frac, N - W * (1 - t) / frac, W + (t - frac) / mid))
    ax.set_xscale("function", functions=(fwd, inv))
    ax.set_yscale("log")
    ax.set_xlim(0, N)
    ylo, yhi = 4e-7, 1.2e-2
    ax.set_ylim(ylo, yhi)

    # junction bands of width B_N
    bands = [(N / 2 - (Kj) * B, N / 2 - Kb * B), (N / 2 + Kb * B, N / 2 + Kj * B),
             ((Jl) * B, (Jl + 1) * B), (N - (Jl + 1) * B, N - Jl * B)]
    for a0, a1 in bands:
        ax.axvspan(a0, a1, color=S["grid"], alpha=0.35, lw=0)
    for xb in (W, N - W):
        ax.axvline(xb, color=S["grid"], lw=0.5, ls=(0, (1, 2)))

    ax.plot(k[1:N], P[1:N], color=S["prior2"], lw=2.6, solid_capstyle="butt", label=r"exact $P_N(k)$", zorder=1)

    def piece(q, z, color, label, lw=1.0):
        qq = np.where(z, q, np.nan)
        ax.plot(k, qq, color=color, lw=lw, label=label, zorder=3)
    ext_bulk = np.abs(y) <= Kj * B
    piece(bulk, ext_bulk, c_bulk, r"bulk $B_N^{-1}h_N$")
    ext_big = (np.abs(y) >= Kb * B) & (dist_end >= Jl * B)
    piece(np.where(k >= N / 2, big_plus, np.nan), ext_big & (k > N / 2), c_big, r"big jump $G_N^{+}$ and mirror")
    piece(np.where(k < N / 2, big_minus, np.nan), ext_big & (k < N / 2), c_big, None)
    ext_layer = (dist_end <= (Jl + 1) * B) & (k >= 1) & (k <= N - 1)
    piece(layer, ext_layer, c_layer, r"boundary $T_\pm(N)\,u_\mp$")
    ax.plot([N], [P[N]], "o", ms=3.5, mfc=S["ink"], mec=S["ink"], zorder=4, label=r"atom $T_+(N)$")
    ax.annotate(r"$P_N(0)=0$", xy=(0, ylo), xytext=(28, 5.6e-7), va="center", fontsize=7, color=S["ink"],
                arrowprops=dict(arrowstyle="-|>", lw=0.5, color=S["ink"], shrinkA=0, shrinkB=0, mutation_scale=5))

    # zone labels
    ytop = 5.0e-3
    lab = dict(fontsize=7, ha="center", va="center", color=S["ink"])
    ax.text(N / 2, ytop, "bulk", **lab)
    ax.text(0.5 * (W + N / 2 - Kj * B), 1.6e-4, "big-jump\nzone", **lab)
    ax.text(0.5 * (N - W + N / 2 + Kj * B), 1.6e-4, "big-jump\nzone", **lab)
    ax.text(0.5 * (W + 2 * B), 3.2e-6, "boundary\nlayer", **lab)
    ax.text(N - 0.5 * (W + 2 * B), 3.2e-6, "boundary\nlayer", **lab)
    ax.annotate("atom", xy=(N, P[N]), xytext=(N - 30, 5.6e-7), fontsize=7, ha="right", va="center",
                color=S["ink"], arrowprops=dict(arrowstyle="-", lw=0.5, color=S["ink"], shrinkA=1, shrinkB=2))
    ax.set_xticks([0, 200, 1000, 2500, 4000, 4800, 5000])
    ax.set_xticklabels(["0", "200", "1000", "2500", "4000", "4800", "5000"])
    ax.set_xlabel(r"$k$")
    ax.set_ylabel(r"$P_N(k)$")
    h_, l_ = ax.get_legend_handles_labels()
    leg1 = ax.legend(h_[:2], l_[:2], loc="upper left", bbox_to_anchor=(0.0, 0.93), frameon=False, fontsize=6.5,
                     handlelength=1.6, borderaxespad=0.2)
    ax.add_artist(leg1)
    ax.legend(h_[2:], l_[2:], loc="upper right", bbox_to_anchor=(1.0, 0.93), frameon=False, fontsize=6.5,
              handlelength=1.6, borderaxespad=0.2)
    style.panel(ax, "a", x=0.015, y=0.97)

    # right panel: the antimode against N
    rows = am["rows"]
    cur = am["curves"]
    Ng = np.array(cur["N"])
    bx.plot(Ng, cur["law"], color=S["prior"], lw=1.0, ls=(0, (4, 2)), label=r"$T_-^{-1}(2\alpha_+ s/N)$")
    bx.step(Ng, cur["refined"], where="post", color=S["exact"], lw=1.0,
            label="refined prediction")
    bx.plot([r["N"] for r in rows], [r["j_star"] for r in rows], "o", ms=3.5, mfc="white", mec=S["ink"],
            mew=0.8, zorder=4, label=r"observed $j^*_N$")
    bx.set_xscale("log")
    bx.set_yscale("log")
    bx.set_xlim(450, 11000)
    bx.set_ylim(5, 70)
    bx.set_xticks([600, 1200, 2400, 4000, 8000])
    bx.set_xticklabels(["600", "1200", "2400", "", "8000"])
    bx.set_yticks([5, 10, 20, 40])
    bx.set_yticklabels(["5", "10", "20", "40"])
    bx.minorticks_off()
    bx.set_xlabel(r"$N$")
    bx.set_ylabel(r"$j^*_N$")
    bx.legend(loc="upper left", bbox_to_anchor=(0.0, 0.9), frameon=False, fontsize=6.5, handlelength=1.8, borderaxespad=0.3)
    style.panel(bx, "b", x=0.03, y=0.97)

    style.save(fig, HERE / "atlas")


if __name__ == "__main__":
    main()
