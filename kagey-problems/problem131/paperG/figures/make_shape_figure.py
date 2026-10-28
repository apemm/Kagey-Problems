"""Figure 1 of Paper G: the Lamperti density and the exact law.

(a) L_{a,1} for a = 0.3, 0.5, a_c = 0.5946..., 0.7 and 0.9, with a_c in the accent color.
(b) N P_N(k) against k/N for the zeta law with a = 0.3 and a = 0.7, the fair start and
    N = 2000, on a logarithmic scale, with L_{a,1}. The end values are far above the density.

Run from the paper folder:  py -I figures/make_shape_figure.py
Writes figures/shape.pdf and figures/shape.png in the shared style ../figures/series_style.py.
"""
import importlib.util
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.optimize import brentq

HERE = Path(__file__).resolve().parent
PAPER = HERE.parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


st = load("series_style", PAPER.parent / "figures" / "series_style.py")
lw = load("lamperti_law", PAPER / "lamperti_law.py")


lc = load("lamperti_critical", PAPER / "lamperti_critical.py")


def main():
    st.use()
    fig, (ax1, ax2, ax3) = plt.subplots(1, 3, figsize=(st.FULL, 2.4), gridspec_kw={"width_ratios": [1.1, 1.1, 0.8]})
    ac = brentq(lambda a: np.cos(np.pi * a / 2) - a, 0.3, 0.9)
    x = np.linspace(0.002, 0.998, 2000)
    alphas = [0.3, 0.5, ac, 0.7, 0.9]
    cols = st.shades(4)
    ci = 0
    for a in alphas:
        if a == ac:
            ax1.plot(x, lw.lamperti(x, a), color=st.SERIES["accent"], lw=1.2,
                     label=r"$\alpha_c=0.5946$")
        else:
            ax1.plot(x, lw.lamperti(x, a), color=cols[ci], label=rf"$\alpha={a}$")
            ci += 1
    ax1.set_ylim(0, 3.2)
    ax1.set_xlim(0, 1)
    ax1.set_xlabel(r"$x$")
    ax1.set_ylabel(r"$L_{\alpha,1}(x)$")
    ax1.legend(frameon=False, loc="upper center", ncol=2, fontsize=7, handlelength=1.5,
               columnspacing=0.8, bbox_to_anchor=(0.5, 1.0))
    st.panel(ax1, "a", y=0.08)

    N = 2000
    k = np.arange(N + 1)
    xx = np.linspace(0.0005, 0.9995, 2000)
    for a, col in ((0.3, cols[0]), (0.7, cols[2])):
        f, T = lw.zeta_law(a, N)
        U = lw.convolution_powers(f, N)
        A, B = lw.arrays(U, U)
        Pp = lw.fresh_plus(A, B, T, T, N)
        P = 0.5 * (Pp + Pp[::-1])
        ax2.semilogy(k / N, N * P, ".", ms=1.0, color=col, label=rf"$NP_N(k)$, $\alpha={a}$")
        ax2.semilogy(xx, lw.lamperti(xx, a), color=st.SERIES["prior"], lw=0.7)
    ax2.plot([], [], color=st.SERIES["prior"], lw=0.7, label=r"$L_{\alpha,1}(k/N)$")
    ax2.set_xlim(-0.02, 1.02)
    ax2.set_ylim(0.15, 400)
    ax2.set_xlabel(r"$k/N$")
    ax2.legend(frameon=False, loc="upper center", fontsize=7, handlelength=1.5, markerscale=4)
    st.panel(ax2, "b", y=0.08)

    a1 = brentq(lambda a: np.sin(np.pi * a) - a, 0.55, 0.95)
    aa = np.linspace(ac + 1e-4, a1 - 1e-4, 400)
    bc = np.array([lc.beta_c(a) for a in aa])
    ax3.plot(aa, bc, color=st.SERIES["accent"], lw=1.0)
    ax3.axvline(ac, color=st.SERIES["prior"], lw=0.6, ls=":")
    ax3.axvline(a1, color=st.SERIES["prior"], lw=0.6, ls=":")
    ax3.set_xlim(0.55, 0.78)
    ax3.set_ylim(0, 4)
    ax3.set_xlabel(r"$\alpha$")
    ax3.set_ylabel(r"$\beta_c(\alpha)$")
    ax3.set_xticks([0.6, 0.65, 0.7, 0.75])
    ax3.text(0.5 * (ac + a1), 1.2, "W", ha="center", fontsize=8)
    ax3.text(0.5 * (ac + a1) - 0.02, 3.4, "U", ha="center", fontsize=8)
    st.panel(ax3, "c", y=0.08)
    fig.tight_layout(w_pad=1.2)
    st.save(fig, HERE / "shape")


if __name__ == "__main__":
    main()
