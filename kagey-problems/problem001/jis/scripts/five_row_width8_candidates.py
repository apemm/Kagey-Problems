r"""Five rows, width 8: every equality candidate checked against every rectangle.

By the equality theorem a blackout of 14 points on the 5 x 8 grid has six double
columns carrying the six edges of a complete bipartite graph K_{2,3} on the rows, one
edge per column, and a singleton in each of the other two columns.  This script lists
all 10 * 8!/2! * 5^2 = 5,040,000 such candidates and checks each one with
verify_narrow.collision, with no SAT solver involved.  It reports the valid ones, their
orbits under row reflection and column reversal, and (as a sanity check) how many
candidates fail.

Coordinates in the JSON output are ONE-BASED (column, row), (1, 1) top left.

Usage:
  python five_row_width8_candidates.py --out ../data/five_row_width8_candidates.json
"""
import argparse
import json
import os
import sys
import time
from itertools import combinations, permutations, product

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, REPO)
import verify_narrow  # noqa: E402

H, M = 5, 8


def candidates():
    for P in combinations(range(H), 2):
        Q = [r for r in range(H) if r not in P]
        edges = [(p, q) for p in P for q in Q]
        for double_cols in combinations(range(M), 6):
            single_cols = [c for c in range(M) if c not in double_cols]
            for order in permutations(edges):
                fixed = [(c, r) for c, e in zip(double_cols, order) for r in e]
                for rows in product(range(H), repeat=len(single_cols)):
                    yield fixed + list(zip(single_cols, rows))


def images(pts):
    maps = [lambda c, r: (c, r), lambda c, r: (c, H - 1 - r),
            lambda c, r: (M - 1 - c, r), lambda c, r: (M - 1 - c, H - 1 - r)]
    return [frozenset(f(c, r) for c, r in pts) for f in maps]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    rects = verify_narrow.rectangles(H, M)
    t0 = time.time()
    total = 0
    valid = []
    for pts in candidates():
        total += 1
        if verify_narrow.collision(rects, verify_narrow.mask(pts, M)) is None:
            valid.append(sorted(pts))
    seconds = time.time() - t0
    assert total == 5040000, total
    orbits = []
    seen = set()
    for pts in valid:
        key = frozenset(pts)
        if key in seen:
            continue
        orb = set(images(pts))
        seen |= orb
        orbits.append(len(orb))
    out = dict(width=M, candidates=total, rectangles=len(rects), valid=len(valid),
               seconds=round(seconds, 1), klein_orbit_sizes=orbits,
               coordinates='one-based (column,row)',
               optima_one_based=[[[c + 1, r + 1] for c, r in p] for p in valid],
               pictures=[[''.join('#' if (c, r) in set(p) else '.' for c in range(M))
                          for r in range(H)] for p in valid])
    print(json.dumps({k: v for k, v in out.items() if k != 'optima_one_based'}, indent=1))
    if args.out:
        with open(args.out, 'w') as f:
            json.dump(out, f, indent=1)


if __name__ == '__main__':
    main()
