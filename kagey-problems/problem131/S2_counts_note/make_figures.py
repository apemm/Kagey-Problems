"""Figures for the note on visit counts.

fig_twins        Example `ex:four`: two chains on four states with the same counts.
                 The time spent in a state has the same law under both (simulated),
                 while the net number of jumps from state 1 to state 2 does not.
fig_information  The six efficiencies of the counts against the horizon T, for one
                 chain on three states (exact, from the N-step chain as in
                 check_information.py).

Run:  python -B make_figures.py     (about two minutes)
The style is in ../figures/dark_style.py.
"""
import sys
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import Ellipse, FancyArrowPatch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "figures"))
sys.path.insert(0, str(HERE))
import dark_style as ds
import check_information as ci

FULL = 6.4
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


def save(fig, name):
    ds.finish(fig)
    fig.savefig(HERE / (name + ".pdf"))
    fig.savefig(HERE / (name + ".png"), dpi=400)
    plt.close(fig)
    print("wrote", name)


# ------------------------------------------------------------------ the two chains
def fix_diag(G):
    G = np.array(G, dtype=float)
    np.fill_diagonal(G, 0.0)
    return G - np.diag(G.sum(1))


def stat(G):
    d = len(G)
    A = np.vstack([G.T[:-1], np.ones(d)])
    b = np.zeros(d)
    b[-1] = 1
    return np.linalg.solve(A, b)


def twins():
    """The chains of Example ex:four (the same numbers as check_lumping_decoder.py)."""
    Lg = fix_diag([[0, 0.9, 0.5], [0.3, 0, 1.1], [0.8, 0.4, 0]])
    mub = stat(Lg)
    nu = np.array([0.35, 0.65])
    Lr = fix_diag((Lg.T * mub[None, :]) / mub[:, None])

    def lift(Lc):
        G = np.zeros((4, 4))
        G[0, 1], G[1, 0] = Lc[0, 1], Lc[1, 0]
        for x in (0, 1):
            G[x, 2], G[x, 3] = Lc[x, 2] * nu
            G[2, x] = G[3, x] = Lc[2, x]
        G[2, 3], G[3, 2] = 1.7, 0.2
        return fix_diag(G)

    mu = np.array([mub[0], mub[1], mub[2] * nu[0], mub[2] * nu[1]])
    return mu, lift(Lg), lift(Lr)


def simulate(mu, G, t, n, seed):
    """n paths on [0, t]. Returns the times in each state and the net number of
    jumps from state 0 to state 1."""
    rng = np.random.default_rng(seed)
    d = len(G)
    q = -np.diag(G)
    jump = G - np.diag(np.diag(G))
    cum = np.cumsum(jump / q[:, None], axis=1)
    state = rng.choice(d, size=n, p=mu)
    clock = np.zeros(n)
    L = np.zeros((n, d))
    net = np.zeros(n, dtype=int)
    alive = np.ones(n, dtype=bool)
    while alive.any():
        idx = np.flatnonzero(alive)
        s = state[idx]
        hold = rng.exponential(1.0 / q[s])
        stay = np.minimum(hold, t - clock[idx])
        np.add.at(L, (idx, s), stay)
        clock[idx] += hold
        go = clock[idx] < t
        alive[idx[~go]] = False
        idx, s = idx[go], s[go]
        new = (rng.random(len(idx))[:, None] > cum[s]).sum(axis=1)
        net[idx] += ((s == 0) & (new == 1)).astype(int) - ((s == 1) & (new == 0)).astype(int)
        state[idx] = new
    return L, net


def draw_chain(ax, G, other, title, color):
    pos = {0: (0.0, 1.0), 1: (0.0, 0.0), 2: (2.4, 1.0), 3: (2.4, 0.0)}
    ax.add_patch(Ellipse((2.4, 0.5), 0.75, 1.8, fc="0.9", ec="0.6", lw=0.5, zorder=0))
    ax.text(2.4, 1.5, "module", ha="center", va="bottom", color="0.4", fontsize=7)
    for i in range(4):
        for j in range(4):
            if i == j or G[i, j] == 0:
                continue
            changed = abs(G[i, j] - other[i, j]) > 1e-9
            a = FancyArrowPatch(pos[i], pos[j], connectionstyle="arc3,rad=0.16",
                                arrowstyle="-|>", mutation_scale=4 + 2.5 * G[i, j],
                                lw=0.3 + 1.0 * G[i, j], shrinkA=8.5, shrinkB=8.5,
                                color=color if changed else "0.5", zorder=1)
            ax.add_patch(a)
    for i, (x, y) in pos.items():
        ax.plot(x, y, "o", ms=13, mfc="white", mec="k", mew=0.8, zorder=3)
        ax.text(x, y, str(i + 1), ha="center", va="center", zorder=4)
    ax.set_xlim(-0.4, 2.95)
    ax.set_ylim(-0.35, 1.8)
    ax.set_aspect("equal")
    ax.axis("off")
    ax.text(0.5, -0.02, title, transform=ax.transAxes, ha="center", va="top")


def fig_twins(n=400000, t=4.0):
    mu, G, G2 = twins()
    L1, net1 = simulate(mu, G, t, n, 1)
    L2, net2 = simulate(mu, G2, t, n, 2)
    fig, axes = plt.subplots(2, 2, figsize=(FULL, 3.7), gridspec_kw={"height_ratios": [1, 1.05]})
    axes = axes.ravel()
    draw_chain(axes[0], G, G2, r"(a) the chain $G$", ds.BLUE)
    draw_chain(axes[1], G2, G, r"(b) the chain $G'$", ds.YELLOW)
    ax = axes[2]
    bins = np.linspace(0, 1, 41)
    x1, x2 = L1[:, 0] / t, L2[:, 0] / t
    inside = (x1 > 0) & (x1 < 1)
    ax.hist(x1[inside], bins=bins, density=True, color=ds.BLUE, alpha=0.9, label="$G$")
    h2, _ = np.histogram(x2[(x2 > 0) & (x2 < 1)], bins=bins, density=True)
    ax.plot(0.5 * (bins[1:] + bins[:-1]), h2, "o", ms=3.0, color=ds.YELLOW, label="$G'$")
    ax.set_xlabel(r"fraction of time in state $1$")
    ax.set_yticks([])
    ax.set_xticks([0, 0.5, 1])
    ax.legend(frameon=False, loc="upper right", handlelength=1.2)
    ax.text(0.04, 0.95, "(c)", transform=ax.transAxes, va="top")
    ax = axes[3]
    ks = np.arange(-5, 6)
    w = 0.38
    ax.bar(ks - w / 2, [(net1 == k).mean() for k in ks], width=w, color=ds.BLUE, label="$G$")
    ax.bar(ks + w / 2, [(net2 == k).mean() for k in ks], width=w, color=ds.YELLOW, label="$G'$")
    ax.set_xlabel(r"jumps $1\to2$ minus jumps $2\to1$")
    ax.set_yticks([])
    ax.set_xticks([-4, -2, 0, 2, 4])
    ax.legend(frameon=False, loc="upper right", handlelength=1.2)
    ax.text(0.04, 0.95, "(d)", transform=ax.transAxes, va="top")
    print("mean of L/t:", np.round(L1.mean(0) / t, 4), np.round(L2.mean(0) / t, 4))
    print("largest gap between the two histograms in (c): %.4f (their heights are about %.2f)"
          % (abs(np.histogram(x1[inside], bins=bins, density=True)[0] - h2).max(), h2.max()))
    print("mean net jumps 1->2:", round(net1.mean(), 4), round(net2.mean(), 4))
    fig.subplots_adjust(wspace=0.12, hspace=0.22)
    save(fig, "fig_twins")


# ------------------------------------------------------------------ the information
def fig_information():
    theta = np.array([1.0, 0.4, 0.7, 1.3, 0.5, 0.9])
    mu = np.array([0.5, 0.3, 0.2])
    Ts = np.exp(np.linspace(np.log(0.03), np.log(20.0), 15))
    fig, axes = plt.subplots(1, 2, figsize=(FULL, 2.3), sharey=True)
    cols = [ds.YELLOW, ds.GOLD, ds.GREEN, ds.TEAL, ds.BLUE, ds.PURPLE]
    for ax, mode, letter, name in zip(axes, ("known", "stationary"), "ab",
                                      ("known start", "stationary start")):
        E = []
        for T in Ts:
            N = 240 if T <= 5 else 400
            IK = ci.fisher_counts(theta, T, N, mode, mu)
            IF = ci.fisher_path(theta, T, N, mode, mu)
            E.append(ci.efficiencies(IK, IF))
        E = np.array(E)
        for k in range(6):
            ax.plot(Ts, E[:, k], "-o", ms=2.2, lw=1.1, color=cols[k])
        ax.set_xscale("log")
        ax.set_yscale("log")
        ax.set_ylim(3e-6, 2.0)
        ax.set_xlabel(r"horizon $T$")
        ax.text(0.04, 0.06, "(%s) %s" % (letter, name), transform=ax.transAxes, va="bottom")
        print(name, "efficiencies at T = %.2f:" % Ts[0], np.round(E[0], 3), " at T = 20:", np.round(E[-1], 4))
    axes[0].set_ylabel("efficiency of the counts")
    fig.subplots_adjust(wspace=0.06)
    save(fig, "fig_information")


if __name__ == "__main__":
    fig_twins()
    if "--twins" not in sys.argv:
        fig_information()
