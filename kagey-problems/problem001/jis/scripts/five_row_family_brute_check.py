r"""Five rows: the width-8 board plus top-row singletons, checked by the definitional oracle.

The family that gives f(5,m) = m+6 for every m >= 8 is the width-8 blackout

    #......#
    ..#...##
    .....##.
    ##...#..
    .####...

(one-based points (1,1), (1,4), (2,4), (2,5), (3,2), (3,5), (4,5), (5,5), (6,3), (6,4),
(7,2), (7,3), (8,1), (8,2)) followed by one top-row singleton in every further column.
five_row_collar_family.py checks it with verify_narrow.collision and with a side-vector
enumerator.  This script is the third check: validity straight from the definition
(injectivity of the presentation map) over rectangles found by testing every 4-subset of
grid points, the oracle of solver/brute.py, at every width from 8 to --brute-max
(default 40; about C(200,4) = 64 million 4-subsets at width 40), and verify_narrow at
every width up to --narrow-max (default 120).  Since restricting a valid blackout to an
interval of columns keeps it valid, the check at the largest width implies the smaller
ones; the smaller widths are checked anyway.

Coordinates in the JSON output are ONE-BASED (column, row), (1, 1) top left.

Usage:
  python five_row_family_brute_check.py --out ../data/five_row_family_brute_check.json
"""
import argparse
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, REPO)
import verify_narrow  # noqa: E402
from solver import brute  # noqa: E402

H = 5
BASE = [(1, 1), (1, 4), (2, 4), (2, 5), (3, 2), (3, 5), (4, 5), (5, 5),
        (6, 3), (6, 4), (7, 2), (7, 3), (8, 1), (8, 2)]


def board(m):
    """One-based points of the family member of width m >= 8."""
    return BASE + [(c, 1) for c in range(9, m + 1)]


def brute_valid(points, m):
    masks, n = brute.rectangle_masks(H, m)
    idx = {p: k for k, p in enumerate(brute.grid_points(H, m))}
    S = sum(1 << idx[p] for p in points)
    return brute.valid(S, masks), len(masks)


def narrow_valid(points, m):
    rects = verify_narrow.rectangles(H, m)
    zero = [(c - 1, r - 1) for c, r in points]
    return verify_narrow.collision(rects, verify_narrow.mask(zero, m)) is None, len(rects)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--brute-max', type=int, default=40)
    ap.add_argument('--narrow-max', type=int, default=120)
    ap.add_argument('--cap', type=int, default=1800)
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    t_start = time.time()
    out = dict(method='definitional oracle (solver/brute.py, all 4-subsets) and verify_narrow',
               coordinates='one-based (column,row)', base_board_one_based=[list(p) for p in BASE],
               base_picture=[''.join('#' if (c, r) in set(BASE) else '.' for c in range(1, 9))
                             for r in range(1, H + 1)],
               brute_checks=[], narrow_checks=[], complete=False)
    for m in range(8, args.brute_max + 1):
        if time.time() - t_start > args.cap:
            break
        t0 = time.time()
        ok, nr = brute_valid(board(m), m)
        out['brute_checks'].append(dict(width=m, points=m + 6, valid=ok, rectangles=nr,
                                        seconds=round(time.time() - t0, 1)))
        print(f'width {m}: brute oracle valid {ok} ({nr} rectangles, {time.time() - t0:.1f}s)',
              flush=True)
        if args.out:
            with open(args.out, 'w') as f:
                json.dump(out, f, indent=1)
    for m in range(8, args.narrow_max + 1):
        ok, nr = narrow_valid(board(m), m)
        out['narrow_checks'].append(dict(width=m, points=m + 6, valid=ok, rectangles=nr))
    print(f"verify_narrow: {sum(c['valid'] for c in out['narrow_checks'])} of "
          f"{len(out['narrow_checks'])} widths valid", flush=True)
    out['all_brute_valid'] = all(c['valid'] for c in out['brute_checks'])
    out['all_narrow_valid'] = all(c['valid'] for c in out['narrow_checks'])
    out['complete'] = len(out['brute_checks']) == args.brute_max - 7
    out['total_seconds'] = round(time.time() - t_start, 1)
    if args.out:
        with open(args.out, 'w') as f:
            json.dump(out, f, indent=1)


if __name__ == '__main__':
    main()
