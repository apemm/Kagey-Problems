"""Padding tests for the width-21 five-row witness (27 black points on 5 x 21).

The witness has singleton row 1 in every column except columns 1, 5, 9, 13, 17, 21 whose black
rows are {1,2}, {1,4}, {2,3}, {3,4}, {2,5}, {4,5} (one-based (column, row)).

Tests, each decided by two rectangle enumerators that share no code (verify_narrow.rectangles,
equal diagonals with a common midpoint, and the 4-subset pairing test of solver/brute.py) and
the definitional collision check:
  1. right padding by k columns of row-1 singletons, k = 1..5 (known: valid for k <= 3, a
     collision at k = 4);
  2. left padding by 5 columns of row-1 singletons (the collar test, W_5 = 5; known valid,
     3658 rectangles);
  3. right padding by k columns of row-5 singletons, k = 1..5 (the collar test on the other
     boundary row; W_5 = 5 columns decide every longer padding);
  4. both at once: 5 row-1 singleton columns on the left and 5 row-5 singleton columns on the
     right.
A collision is reported as the two rectangles and their common visible set, one-based in the
coordinates of the padded board (the original witness keeps columns 1..21 after right padding;
after left padding by k columns it occupies columns k+1..k+21).

Usage: python five_row_padding.py [--out FILE]
"""
import argparse
import json
import os
import time

from five_row_common import (DATA_DIR, collision_report, mask_of, one_based, published_witness,
                             rectangles_by_quads, verify_narrow)

ROWS = 5


def padded(points, left, right, left_row, right_row):
    """Shift the witness right by `left` columns and add singleton columns on both sides."""
    cols = 21 + left + right
    pts = [(x + left, y) for x, y in points]
    pts += [(x, left_row) for x in range(left)]
    pts += [(21 + left + x, right_row) for x in range(right)]
    return cols, sorted(pts)


def test(points, cols, label):
    t0 = time.time()
    rects_a = verify_narrow.rectangles(ROWS, cols)
    rects_b = rectangles_by_quads(ROWS, cols)
    mask = mask_of(points, cols)
    rep_a = collision_report(rects_a, mask, ROWS, cols)
    rep_b = collision_report(rects_b, mask, ROWS, cols)
    return {'test': label, 'cols': cols, 'black_points': len(points),
            'rectangles_equal_diagonals': len(rects_a), 'rectangles_four_subsets': len(rects_b),
            'enumerators_agree': rects_a == rects_b,
            'valid_equal_diagonals': rep_a is None, 'valid_four_subsets': rep_b is None,
            'collision_equal_diagonals': rep_a, 'collision_four_subsets': rep_b,
            'points': one_based(points), 'seconds': round(time.time() - t0, 2)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', default=os.path.join(DATA_DIR, 'five_row_padding.json'))
    args = ap.parse_args()
    w = published_witness()
    tests = [test(w, 21, 'witness alone')]
    for k in range(1, 6):
        cols, pts = padded(w, 0, k, 0, 0)
        tests.append(test(pts, cols, f'right padding, {k} row-1 singleton columns'))
    cols, pts = padded(w, 5, 0, 0, 0)
    tests.append(test(pts, cols, 'left padding, 5 row-1 singleton columns (collar W_5 = 5)'))
    for k in range(1, 6):
        cols, pts = padded(w, 0, k, 0, ROWS - 1)
        tests.append(test(pts, cols, f'right padding, {k} row-5 singleton columns'))
    cols, pts = padded(w, 5, 5, 0, ROWS - 1)
    tests.append(test(pts, cols, 'left 5 row-1 singleton columns and right 5 row-5 singleton columns'))
    out = {'witness_one_based': one_based(w),
           'coordinates': 'one-based (column, row) of the padded board, (1,1) top-left',
           'tests': tests}
    with open(args.out, 'w') as f:
        json.dump(out, f, indent=1)
    for t in tests:
        print(f"{t['test']}: cols={t['cols']} rects={t['rectangles_equal_diagonals']}/"
              f"{t['rectangles_four_subsets']} valid={t['valid_equal_diagonals']}/"
              f"{t['valid_four_subsets']} collision={t['collision_equal_diagonals']} "
              f"({t['seconds']} s)")


if __name__ == '__main__':
    main()
