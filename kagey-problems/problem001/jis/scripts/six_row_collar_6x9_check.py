"""Collar test boards for the stored 16-point blackouts of the 6 x 9 grid.

Reads jis/data/small_cells_sat_6x9_b16.json, which holds three witnesses (one per SAT run).
For each witness it builds the collar test board of Theorem "collar" with the padding row 1
on both sides: W_6 = 7 columns black only in row 1 on the left, the witness shifted right by
7 columns, and 7 more such columns on the right, a 6 x 23 board. It then checks each board
from the definition with two enumerators that share no code:

  vectors  every rectangle {p, p+u, p+v, p+u+v} with u . v = 0 (this file)
  brute    solver/brute.py, which tests every 4-subset of points (slow by design)

Only the first witness (run 0, encoding A on CaDiCaL 1.5.3) is cited in the paper.
Usage: python six_row_collar_6x9_check.py
"""
import json
import math
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, ROOT)

from solver.brute import grid_points, rectangle_masks, valid  # noqa: E402

ROWS, PAD = 6, 7


def vector_rectangles(rows, cols):
    """All rectangles with corners on the grid, as frozensets of (column, row)."""
    pts = [(i, j) for i in range(1, cols + 1) for j in range(1, rows + 1)]
    inside = set(pts)
    rects = set()
    for (x, y) in pts:
        for ux in range(-cols, cols + 1):
            for uy in range(-rows, rows + 1):
                if (ux, uy) == (0, 0):
                    continue
                # v is a nonzero multiple of the primitive vector (-uy, ux) / g
                g = math.gcd(ux, uy)
                for k in range(-max(rows, cols), max(rows, cols) + 1):
                    if k == 0:
                        continue
                    vx, vy = -uy // g * k, ux // g * k
                    c = [(x, y), (x + ux, y + uy), (x + vx, y + vy), (x + ux + vx, y + uy + vy)]
                    if all(p in inside for p in c):
                        rects.add(frozenset(c))
    return rects


def valid_vectors(S, rects):
    seen = {}
    for R in rects:
        P = frozenset(R - S)
        if P in seen:
            return False, sorted(sorted(seen[P])), sorted(sorted(R))
        seen[P] = R
    return True, None, None


def board(witness):
    pts = {(c, 1) for c in range(1, PAD + 1)}
    pts |= {(c + PAD, r) for c, r in witness}
    pts |= {(c, 1) for c in range(PAD + 10, 2 * PAD + 10)}
    return pts, 2 * PAD + 9


def main():
    src = os.path.join(ROOT, 'jis', 'data', 'small_cells_sat_6x9_b16.json')
    data = json.load(open(src))
    width = 2 * PAD + 9
    t0 = time.time()
    rects = vector_rectangles(ROWS, width)
    masks, _ = rectangle_masks(ROWS, width)
    idx = {p: k for k, p in enumerate(grid_points(ROWS, width))}
    out = {'source': os.path.basename(src), 'rows': ROWS, 'board_width': width,
           'padding': 'seven columns black only in row 1 on each side',
           'rectangles_vectors': len(rects), 'rectangles_brute': len(masks), 'runs': []}
    for k, run in enumerate(data['runs']):
        S, w = board([tuple(p) for p in run['witness']])
        ok_v, r1, r2 = valid_vectors(S, rects)
        ok_b = valid(sum(1 << idx[p] for p in S), masks)
        rec = {'run': k, 'encoding': run['encoding'], 'solver': run['solver'],
               'witness': run['witness'], 'board_size': len(S),
               'valid_by_vectors': ok_v, 'valid_by_brute': ok_b}
        if not ok_v:
            rec['example_clash'] = [r1, r2]
        out['runs'].append(rec)
        print(json.dumps({k2: rec[k2] for k2 in rec if k2 != 'witness'}), flush=True)
    out['seconds'] = round(time.time() - t0, 1)
    with open(os.path.join(ROOT, 'jis', 'data', 'six_row_collar_6x9_check.json'), 'w') as fh:
        json.dump(out, fh, indent=1)


if __name__ == '__main__':
    main()
