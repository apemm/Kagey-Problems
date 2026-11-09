"""Uniformly spaced alternating seas: for each gap D, try random edge orders and count valid boards,
and count boards hit by the Lemma 7 family (double point (0,c), c = 2s+1, row-1 point at s^2 - 1,
horizontal pair in row s + 1... detected as a horizontal rival). Usage: python uniform_alt.py h Dmin Dmax trials"""
import sys, random
from fastcheck import violations


def board(h, order, D, margin):
    cols = [{1}] * margin
    row = 1
    for j, e in enumerate(order):
        if j:
            cols += [{row}] * (D - 1)
        cols.append(set(e))
        row = h if row == 1 else 1
    cols += [{row}] * margin
    return cols


def main():
    h, Dmin, Dmax, trials = map(int, sys.argv[1:5])
    E = [(a, b) for a in range(1, h + 1) for b in range(a + 1, h + 1) if (b - a) % 2]
    rng = random.Random(3)
    W = 1 + (h - 1) ** 2 // 4
    for D in range(Dmin, Dmax + 1):
        ok = 0
        for _ in range(trials):
            order = E[:]
            rng.shuffle(order)
            if violations(h, board(h, order, D, W + 2), stop=True) == 0:
                ok += 1
        print('h', h, 'D', D, 'valid', ok, 'of', trials, flush=True)


if __name__ == '__main__':
    main()
