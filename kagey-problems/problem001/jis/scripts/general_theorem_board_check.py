"""Check the alternating-boundary-sea construction of notes/general_theorem_gadgets.md on full boards.

For h rows, pick a random balanced partition of the rows (seeded), put one double column on each
edge of the complete bipartite graph in a random order, with 2 W_h + 1 sea columns between
consecutive doubles, and a random number (0 to 3) of sea columns at each end. Sea columns are
black in one boundary row only: row 1 before the first double, then row h, then row 1, and so on,
switching at every double. The board is checked from the definition with verify_narrow.collision.
It should be valid with exactly floor(h^2/4) points more than its width.

Usage: python general_theorem_board_check.py H SEED
Results of the runs so far: h = 5, 6, 7 (seeds 1, 2) and h = 8 (seed 3), all valid; see
jis/data/general_theorem_board_check.txt.
"""
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.abspath(os.path.join(HERE, '..', '..')))
from verify_narrow import collision, mask, rectangles  # noqa: E402


def board(h, edges, gap, lpad, rpad):
    cols = []
    sea = [1, h]
    k = 0
    cols += [{sea[k % 2]}] * lpad
    for i, e in enumerate(edges):
        if i:
            cols += [{sea[k % 2]}] * gap
        cols.append(set(e))
        k += 1
    cols += [{sea[k % 2]}] * rpad
    return cols


def check(h, cols):
    m = len(cols)
    pts = [(x, r - 1) for x, c in enumerate(cols) for r in c]
    c = collision(rectangles(h, m), mask(pts, m))
    return m, len(pts) - m, c is None


def main():
    h, seed = int(sys.argv[1]), int(sys.argv[2])
    W = 1 + (h - 1) ** 2 // 4
    rng = random.Random(seed)
    rows = list(range(1, h + 1))
    rng.shuffle(rows)
    P, Q = sorted(rows[:h // 2]), sorted(rows[h // 2:])
    edges = [(a, b) for a in P for b in Q]
    rng.shuffle(edges)
    t = time.time()
    m, ex, ok = check(h, board(h, edges, 2 * W + 1, rng.randint(0, 3), rng.randint(0, 3)))
    print(f'h={h} partition={P}|{Q} width={m} excess={ex} q_h={h * h // 4} valid={ok} '
          f'({time.time() - t:.0f}s)', flush=True)


if __name__ == '__main__':
    main()
