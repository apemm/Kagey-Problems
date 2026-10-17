r"""Five rows, staircase-plus-one blackouts of m+5 points.

A staircase is a monotone lattice path from the top-left point (1,1) to the bottom-right
point (m,5), one step right or down at a time: m+4 points.  This script looks for a
valid blackout consisting of a staircase plus one more point (m+5 points), the shape the
game in game/ used for its excess-5 witnesses.  Staircases are taken in lexicographic
order of their down-step positions and the extra point in reading order; the search
stops at the first valid board, so the output is a witness and the number of boards
tested, not a count.  With --count the search runs to the end and reports the number of
valid staircase-plus-one boards (each staircase-plus-one set counted once).

Validity is checked with verify_narrow.collision against verify_narrow.rectangles.
Coordinates in the JSON output are ONE-BASED (column, row), (1, 1) top left.

Usage:
  python five_row_staircase_witness.py --widths 11 12 13 14 15 16
                                       --out ../data/five_row_staircase_witnesses.json
"""
import argparse
import json
import os
import sys
import time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, REPO)
import verify_narrow  # noqa: E402

H = 5


def staircases(m):
    """Zero-based point sets of monotone paths from (0,0) to (m-1,H-1)."""
    steps = m - 1 + H - 1
    for downs in combinations(range(steps), H - 1):
        x = y = 0
        pts = [(0, 0)]
        down = set(downs)
        for s in range(steps):
            if s in down:
                y += 1
            else:
                x += 1
            pts.append((x, y))
        yield pts


def search(m, count_all=False, cap=1800):
    rects = verify_narrow.rectangles(H, m)
    t0 = time.time()
    tested = 0
    found = None
    valid_sets = set()
    staircase_valid = 0
    n_stairs = 0
    for pts in staircases(m):
        n_stairs += 1
        base = verify_narrow.mask(pts, m)
        if verify_narrow.collision(rects, base) is None:
            staircase_valid += 1
        on_path = set(pts)
        for y in range(H):
            for x in range(m):
                if (x, y) in on_path:
                    continue
                tested += 1
                black = base | (1 << (y * m + x))
                if verify_narrow.collision(rects, black) is None:
                    if found is None:
                        found = sorted(pts + [(x, y)])
                    if count_all:
                        valid_sets.add(black)
                    else:
                        break
            if found is not None and not count_all:
                break
        if found is not None and not count_all:
            break
        if time.time() - t0 > cap:
            break
    out = dict(width=m, rectangles=len(rects), staircases_tried=n_stairs,
               boards_tested=tested, seconds=round(time.time() - t0, 2),
               staircase_plus_one_exists=found is not None)
    if found is not None:
        out['witness_one_based'] = [[c + 1, r + 1] for c, r in found]
        out['witness_picture'] = [''.join('#' if (c, r) in set(found) else '.'
                                          for c in range(m)) for r in range(H)]
    if count_all:
        out['valid_staircases'] = staircase_valid
        out['valid_staircase_plus_one_boards'] = len(valid_sets)
        out['complete'] = time.time() - t0 <= cap
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--widths', type=int, nargs='+', default=list(range(11, 17)))
    ap.add_argument('--count', action='store_true')
    ap.add_argument('--cap', type=int, default=1800)
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    results = dict(method='staircase plus one point, checked by verify_narrow.collision',
                   coordinates='one-based (column,row)', instances=[])
    for m in args.widths:
        r = search(m, args.count, args.cap)
        results['instances'].append(r)
        print(f"width {m}: exists {r['staircase_plus_one_exists']} after {r['boards_tested']} "
              f"boards, {r['seconds']}s" +
              (f"; valid boards {r.get('valid_staircase_plus_one_boards')}" if args.count else ''),
              flush=True)
        if args.out:
            with open(args.out, 'w') as f:
                json.dump(results, f, indent=1)


if __name__ == '__main__':
    main()
