"""Shared helpers for the five-row computations in jis/.

Conventions. Internally a point is (x, y) zero-based with x the column and y the row, and a
blackout is a bitmask with bit y*cols + x, exactly as in verify_narrow.py at the repository
root. Every JSON file written by the scripts in this folder translates to ONE-BASED
(column, row) with (1,1) the top-left point, matching PROBLEM.md.

verify_narrow.py (standard library, equal-diagonal rectangle enumerator) is imported from the
repository root for the independent validity checks.
"""
import os
import sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

import verify_narrow  # noqa: E402

DATA_DIR = os.path.join(HERE, '..', 'data')


def bit(x, y, cols):
    return 1 << (y * cols + x)


def points_of(mask, rows, cols):
    """Zero-based (x, y) points of a bitmask, sorted by column then row."""
    return sorted((x, y) for y in range(rows) for x in range(cols) if mask >> (y * cols + x) & 1)


def mask_of(points, cols):
    return sum(1 << (y * cols + x) for x, y in set(points))


def one_based(points):
    return [[x + 1, y + 1] for x, y in points]


def zero_based(points):
    return [(x - 1, y - 1) for x, y in points]


def corners_of(rect_mask, rows, cols):
    return points_of(rect_mask, rows, cols)


def rectangles_by_quads(rows, cols):
    """Rectangle corner masks found by testing every 4-subset of points (the pairing test of
    solver/brute.py: some pairing into two diagonals has equal midpoints and equal lengths).
    Shares no code with verify_narrow.rectangles; used as the second enumerator."""
    pts = [(x, y) for y in range(rows) for x in range(cols)]
    out = set()
    for p, q, r, s in combinations(pts, 4):
        for (a, b), (c, d) in (((p, q), (r, s)), ((p, r), (q, s)), ((p, s), (q, r))):
            if (a[0] + b[0], a[1] + b[1]) == (c[0] + d[0], c[1] + d[1]) and \
               (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2 == (c[0] - d[0]) ** 2 + (c[1] - d[1]) ** 2:
                out.add(mask_of((p, q, r, s), cols))
                break
    return sorted(out)


def difference_sets(rects):
    """Distinct symmetric differences of corner sets over all pairs of distinct rectangles."""
    return {a ^ b for a, b in combinations(rects, 2)}


def prune_supersets(masks):
    """Drop every mask that strictly contains another mask of the family (its clause is
    implied). Masks have at most 8 bits, so subsets are enumerated directly."""
    family = set(masks)
    kept = []
    for m in sorted(family, key=lambda v: v.bit_count()):
        bits = [1 << i for i in range(m.bit_length()) if m >> i & 1]
        redundant = False
        for k in range(1, len(bits)):
            for sub in combinations(bits, k):
                if sum(sub) in family:
                    redundant = True
                    break
            if redundant:
                break
        if not redundant:
            kept.append(m)
    return kept


def published_witness(cols=21):
    """The width-21 five-row witness, zero-based: singleton row 0 in every column except
    0, 4, 8, 12, 16, 20 whose black rows are 01, 03, 12, 23, 14, 34 (one-based: row 1
    singletons except columns 1, 5, 9, 13, 17, 21 with row pairs {1,2}, {1,4}, {2,3}, {3,4},
    {2,5}, {4,5})."""
    assert cols == 21
    doubles = {0: (0, 1), 4: (0, 3), 8: (1, 2), 12: (2, 3), 16: (1, 4), 20: (3, 4)}
    pts = set()
    for x in range(cols):
        if x in doubles:
            for y in doubles[x]:
                pts.add((x, y))
        else:
            pts.add((x, 0))
    return sorted(pts)


def klein_images(points, rows, cols):
    """The four images of a point set under row reflection y -> rows-1-y and column reversal
    x -> cols-1-x (zero-based), as sorted tuples: identity, row reflection, column reversal,
    half turn."""
    maps = [lambda x, y: (x, y), lambda x, y: (x, rows - 1 - y),
            lambda x, y: (cols - 1 - x, y), lambda x, y: (cols - 1 - x, rows - 1 - y)]
    return [tuple(sorted(f(x, y) for x, y in points)) for f in maps]


def column_profile(points, rows, cols):
    """Per-column sorted tuple of black rows."""
    prof = [[] for _ in range(cols)]
    for x, y in points:
        prof[x].append(y)
    return [tuple(sorted(p)) for p in prof]


def collision_report(rects, mask, rows, cols):
    """None if valid, else the two colliding rectangles and their common presentation,
    all ONE-BASED."""
    pair = verify_narrow.collision(rects, mask)
    if pair is None:
        return None
    a, b = pair
    return {'rectangle_1': one_based(corners_of(a, rows, cols)),
            'rectangle_2': one_based(corners_of(b, rows, cols)),
            'visible': one_based(points_of(a & ~mask, rows, cols))}
