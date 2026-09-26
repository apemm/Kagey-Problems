"""Galton board animation for Problem 131.

Four boards side by side, at p = 1/2, 2/3, 5/6 and 0.95. The first bounce of
each ball is fair and every later bounce repeats the previous direction with
probability p. The histograms below the boards fill as the balls land, and
the black outline is the exact law P_N(k) of Theorem 2.1, so the viewer can
watch each histogram settle onto it. At p = 1/2 this is the usual binomial
board. As p grows the middle empties into the two end bins. At N = 10 the
middle and the ends tie at p_10 = 0.8384, so at 5/6 the middle is still just
above the ends, and at 0.95 the ends dominate.

  python animate.py

Writes galton.gif next to this script always, and galton.mp4 when an ffmpeg
binary is available (through the imageio-ffmpeg package if it is installed).
It takes pmf_exact and shades from ../paperA/figures/make_figures.py.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.animation import FFMpegWriter, FuncAnimation, PillowWriter

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "paperA" / "figures"))
from make_figures import pmf_exact, shades

OUT = Path(__file__).resolve().parent

N = 10                  # bounces, so N + 1 = 11 bins (Kagey's row 11)
PS = [Fraction(1, 2), Fraction(2, 3), Fraction(5, 6), Fraction(19, 20)]
FPS = 20
ROW = 3                 # frames per row of pegs
FLIGHT = ROW * (N + 1)  # frames from release to landing
RELEASE = 240           # frames during which balls are released
HOLD = 50               # frames at the end with the final histograms
SEED = 131

try:
    import imageio_ffmpeg
    matplotlib.rcParams["animation.ffmpeg_path"] = imageio_ffmpeg.get_ffmpeg_exe()
    HAVE_FFMPEG = True
except Exception:
    HAVE_FFMPEG = False


def release_times():
    """Frame at which each ball is released: slow at first, then faster."""
    rate = np.minimum(0.25 * 1.03 ** np.arange(RELEASE), 20.0)
    total = np.floor(np.cumsum(rate)).astype(int)
    return np.repeat(np.arange(RELEASE), np.diff(np.r_[0, total]))


def words(p, n_balls, rng):
    """Bounce directions (+1 right, -1 left): fair first bounce, then persistence p."""
    e = np.empty((n_balls, N), dtype=int)
    e[:, 0] = rng.choice([-1, 1], n_balls)
    keep = rng.random((n_balls, N - 1)) < p
    for i in range(1, N):
        e[:, i] = np.where(keep[:, i - 1], e[:, i - 1], -e[:, i - 1])
    return e


def positions(e, age):
    """(x, y) of balls of the given ages (frames since release)."""
    s = np.clip(age / ROW, 0, N + 1)          # rows travelled, fractional
    i = np.floor(s).astype(int)
    f = s - i
    csum = np.c_[np.zeros(len(e), dtype=int), np.cumsum(e, axis=1)] / 2   # x after i bounces
    x0 = csum[np.arange(len(e)), np.clip(i - 1, 0, N)]
    x1 = csum[np.arange(len(e)), np.clip(i, 0, N)]
    x = np.where(i == 0, 0.0, x0 + (x1 - x0) * f)
    # a small hop off each peg
    y = -(s - 0.4) + np.where(i >= 1, 0.35 * np.sin(np.pi * f), 0.0)
    return x, y


def main():
    OUT.mkdir(exist_ok=True)
    rng = np.random.default_rng(SEED)
    t_rel = release_times()
    n_balls = len(t_rel)
    frames = RELEASE + FLIGHT + HOLD
    cols = shades(4, hi=0.8)
    plt.rcParams.update({"font.size": 10, "font.family": "serif", "mathtext.fontset": "cm"})
    fig = plt.figure(figsize=(9.6, 5.0), dpi=100)
    gs = fig.add_gridspec(2, 4, height_ratios=[1.25, 1.0], hspace=0.05, wspace=0.12,
                          left=0.03, right=0.99, top=0.9, bottom=0.08)
    fig.suptitle(rf"Persistent Galton board, $N={N}$ bounces: first bounce fair, "
                 r"then repeat with probability $p$", fontsize=11)
    boards = []
    for c, p in enumerate(PS):
        exact = np.array([float(v) for v in pmf_exact(N, p)])
        e = words(float(p), n_balls, rng)
        k_final = (e > 0).sum(axis=1)
        ax = fig.add_subplot(gs[0, c])
        hx = fig.add_subplot(gs[1, c])
        for i in range(1, N + 1):
            xs = np.arange(i) - (i - 1) / 2
            ax.plot(xs, np.full(i, -i), "o", ms=2.6, color="0.45")
        ax.set_xlim(-N / 2 - 0.8, N / 2 + 0.8)
        ax.set_ylim(-N - 1.0, 0.9)
        ax.axis("off")
        ax.set_title(rf"$p={p.numerator}/{p.denominator}$", fontsize=11, pad=0)
        dots = ax.scatter([], [], s=7, color=cols[c], edgecolors="none")
        kk = np.arange(N + 1) - N / 2
        bars = hx.bar(kk, np.zeros(N + 1), width=0.8, color=cols[c], alpha=0.85)
        hx.stairs(exact, np.r_[kk - 0.5, kk[-1] + 0.5], color="k", lw=1.2, baseline=None)
        hx.set_xlim(-N / 2 - 0.8, N / 2 + 0.8)
        hx.set_ylim(0, 1.3 * exact.max())
        hx.set_xticks(kk[::5], [str(int(k + N / 2)) for k in kk[::5]])
        hx.tick_params(left=False, right=False, top=False, labelleft=False, direction="in")
        for s in ("top", "right", "left"):
            hx.spines[s].set_visible(False)
        label = hx.text(0.03, 0.97, "", transform=hx.transAxes, va="top", fontsize=9)
        boards.append(dict(e=e, k=k_final, dots=dots, bars=bars, label=label))
    fig.text(0.5, 0.015, r"bin $k$ (black outline: exact law $P_N(k)$)", ha="center", fontsize=10)

    def update(f):
        artists = []
        age = f - t_rel
        flying = (age >= 0) & (age < FLIGHT)
        landed = age >= FLIGHT
        n = landed.sum()
        for b in boards:
            x, y = positions(b["e"][flying], age[flying])
            b["dots"].set_offsets(np.c_[x, y] if len(x) else np.empty((0, 2)))
            counts = np.bincount(b["k"][landed], minlength=N + 1) / max(n, 1)
            for bar, h in zip(b["bars"], counts):
                bar.set_height(h)
            b["label"].set_text(f"{n} balls")
            artists += [b["dots"], b["label"], *b["bars"]]
        return artists

    anim = FuncAnimation(fig, update, frames=frames, blit=False)
    anim.save(OUT / "galton.gif", writer=PillowWriter(fps=FPS))
    print(f"wrote galton.gif ({(OUT / 'galton.gif').stat().st_size / 2**20:.1f} MB, {n_balls} balls per board)")
    if HAVE_FFMPEG:
        anim.save(OUT / "galton.mp4", writer=FFMpegWriter(fps=FPS, bitrate=2400))
        print("wrote galton.mp4")
    plt.close(fig)


if __name__ == "__main__":
    main()
