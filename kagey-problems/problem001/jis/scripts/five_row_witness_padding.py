"""Padding tests for the width-21 five-row witness of 27 points, with two rectangle
enumerators that share no code (verify_narrow.rectangles, equal diagonals with a common
midpoint; five_row_sidevec.rectangles_sidevec, corner plus perpendicular side vectors) and
two validity tests (verify_narrow.collision; injectivity of the presentation map).

The witness (one-based (column, row)): row-1 singletons in every column except columns
1, 5, 9, 13, 17, 21, whose black rows are {1,2}, {1,4}, {2,3}, {3,4}, {2,5}, {4,5}.

Tests:
  1. the witness alone;
  2. right padding by k columns of row-1 singletons, k = 1..5 (expected: valid for k <= 3,
     a collision at k = 4 between the axis rectangle (20,1),(20,3),(25,1),(25,3) and the
     tilted rectangle (20,3),(21,5),(24,1),(25,3), both showing {(20,3),(25,3)});
  3. left padding by 5 columns of row-1 singletons (the collar width W_5 = 5; expected valid,
     3658 rectangles);
  4. right padding by k columns of row-5 singletons, k = 1..5 (the two-sided question);
  5. the half-turn image of the witness (rows j -> 6-j, columns i -> 22-i), which has its
     singletons in row 5, and whether it equals the witness.
Coordinates in the output are one-based on the padded board; after left padding by k columns
the witness occupies columns k+1..k+21.

Usage: python five_row_witness_padding.py [--out FILE]
"""
import argparse
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, ROOT)
import verify_narrow  # noqa: E402
from five_row_sidevec import presentations_injective, rectangles_sidevec  # noqa: E402

DATA_DIR = os.path.join(HERE, '..', 'data')
ROWS = 5
DOUBLES = {1: (1, 2), 5: (1, 4), 9: (2, 3), 13: (3, 4), 17: (2, 5), 21: (4, 5)}   # one-based


def witness():
    pts = set()
    for x in range(1, 22):
        if x in DOUBLES:
            pts.update((x, y) for y in DOUBLES[x])
        else:
            pts.add((x, 1))
    return sorted(pts)


def mask_of(points, cols):
    """points one-based (column, row) -> bitmask with bit (row-1)*cols + (column-1)."""
    return sum(1 << ((y - 1) * cols + (x - 1)) for x, y in set(points))


def points_of(mask, cols):
    return [[i % cols + 1, i // cols + 1] for i in range(mask.bit_length()) if mask >> i & 1]


def run(label, points, cols):
    t0 = time.time()
    ra = verify_narrow.rectangles(ROWS, cols)
    rb = rectangles_sidevec(ROWS, cols)
    m = mask_of(points, cols)
    pa = verify_narrow.collision(ra, m)
    ok_b, pb = presentations_injective(rb, m)
    rec = {'test': label, 'cols': cols, 'black_points': len(set(points)),
           'rectangles_equal_diagonals': len(ra), 'rectangles_side_vectors': len(rb),
           'enumerators_agree': ra == rb,
           'valid_equal_diagonals_collision': pa is None,
           'valid_side_vectors_injective': ok_b,
           'collision': None, 'points': [list(p) for p in sorted(set(points))],
           'seconds': round(time.time() - t0, 2)}
    if pa is not None:
        a, b = pa
        rec['collision'] = {'rectangle_1': points_of(a, cols), 'rectangle_2': points_of(b, cols),
                            'visible': points_of(a & ~m, cols)}
    if pb is not None:
        a, b = pb
        rec['collision_side_vectors'] = {'rectangle_1': points_of(a, cols),
                                         'rectangle_2': points_of(b, cols),
                                         'visible': points_of(a & ~m, cols)}
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', default=os.path.join(DATA_DIR, 'five_row_witness_padding.json'))
    args = ap.parse_args()
    w = witness()
    tests = [run('witness alone', w, 21)]
    for k in range(1, 6):
        pts = w + [(21 + i, 1) for i in range(1, k + 1)]
        tests.append(run(f'right padding, {k} row-1 singleton columns', pts, 21 + k))
    pts = [(x + 5, y) for x, y in w] + [(i, 1) for i in range(1, 6)]
    tests.append(run('left padding, 5 row-1 singleton columns', pts, 26))
    for k in range(1, 6):
        pts = w + [(21 + i, 5) for i in range(1, k + 1)]
        tests.append(run(f'right padding, {k} row-5 singleton columns', pts, 21 + k))
    half_turn = sorted((22 - x, 6 - y) for x, y in w)
    tests.append(run('half-turn image of the witness', half_turn, 21))
    summary = {
        'witness': [list(p) for p in w],
        'half_turn_image': [list(p) for p in half_turn],
        'witness_fixed_by_half_turn': half_turn == w,
        'witness_fixed_by_row_reflection': sorted((x, 6 - y) for x, y in w) == w,
        'witness_fixed_by_column_reversal': sorted((22 - x, y) for x, y in w) == w,
        'klein_orbit_size': len({tuple(w), tuple(half_turn),
                                 tuple(sorted((x, 6 - y) for x, y in w)),
                                 tuple(sorted((22 - x, y) for x, y in w))}),
        'coordinates': 'one-based (column, row) on the padded board, (1,1) top-left',
        'tests': tests,
    }
    with open(args.out, 'w') as f:
        json.dump(summary, f, indent=1)
    for t in tests:
        print(f"{t['test']}: cols={t['cols']} rects={t['rectangles_equal_diagonals']}/"
              f"{t['rectangles_side_vectors']} agree={t['enumerators_agree']} "
              f"valid={t['valid_equal_diagonals_collision']}/{t['valid_side_vectors_injective']} "
              f"collision={t['collision']} ({t['seconds']} s)")
    print('witness fixed by half turn:', summary['witness_fixed_by_half_turn'],
          '; Klein orbit size:', summary['klein_orbit_size'])
    print('->', args.out)


if __name__ == '__main__':
    main()
