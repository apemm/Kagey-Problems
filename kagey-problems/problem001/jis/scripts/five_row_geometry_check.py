"""Rectangle enumeration by right-angle triples and the presentation test.

This module is a second, separately written implementation of the two
primitives behind every five-row claim: the list of all rectangles (tilted
included) with corners on an h x m grid, and the test that a blackout leaves
every rectangle identifiable from its visible corners.

Rectangles are found from a corner P and two perpendicular side vectors
v, w (v . w = 0): the corners are P, P+v, P+w, P+v+w.  Nothing is shared with
verify_narrow.py, whose enumerator pairs equal diagonals with a common
midpoint; the two lists are compared in main().

Coordinates inside this module are zero-based (x = column, y = row); the
bit of (x, y) is y * cols + x, the same convention as verify_narrow.py so
masks can be compared directly.  Functions that take or give point lists in
one-based (column, row) form say so in their names.
"""
import os
import sys
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
PROBLEM_DIR = os.path.abspath(os.path.join(HERE, '..', '..'))


def rectangles_by_sides(rows, cols):
    """All rectangles with corners on the grid, as sorted bit masks."""
    found = set()
    for y in range(rows):
        for x in range(cols):
            for b in range(-(rows - 1), rows):
                for a in range(-(cols - 1), cols):
                    if a == 0 and b == 0:
                        continue
                    qx, qy = x + a, y + b
                    if not (0 <= qx < cols and 0 <= qy < rows):
                        continue
                    g = gcd(abs(a), abs(b))
                    px, py = -b // g, a // g        # primitive perpendicular
                    t = 1
                    while True:
                        rx, ry = x + t * px, y + t * py
                        sx, sy = qx + t * px, qy + t * py
                        if not (0 <= rx < cols and 0 <= ry < rows
                                and 0 <= sx < cols and 0 <= sy < rows):
                            break
                        m = ((1 << (y * cols + x)) | (1 << (qy * cols + qx))
                             | (1 << (ry * cols + rx)) | (1 << (sy * cols + sx)))
                        found.add(m)
                        t += 1
    return sorted(found)


def rectangles_by_max_column(rows, cols):
    """Rectangles grouped by their rightmost column (for column-by-column searches)."""
    groups = [[] for _ in range(cols)]
    for m in rectangles_by_sides(rows, cols):
        last = 0
        mm = m
        while mm:
            bit = mm.bit_length() - 1
            last = max(last, bit % cols)
            mm ^= 1 << bit
        groups[last].append(m)
    return groups


def presentation_collision(rects, black):
    """Two rectangles with the same visible corner set, or None if the blackout is valid."""
    seen = {}
    for r in rects:
        shown = r & ~black
        other = seen.get(shown)
        if other is not None:
            return other, r
        seen[shown] = r
    return None


def mask_from_one_based(points, cols):
    """Bit mask of a list of one-based (column, row) points."""
    m = 0
    for c, r in points:
        m |= 1 << ((r - 1) * cols + (c - 1))
    return m


def one_based_from_mask(black, rows, cols):
    return [(x + 1, y + 1) for y in range(rows) for x in range(cols)
            if black >> (y * cols + x) & 1]


def picture(black, rows, cols):
    return [''.join('#' if black >> (y * cols + x) & 1 else '.' for x in range(cols))
            for y in range(rows)]


def main():
    sys.path.insert(0, PROBLEM_DIR)
    import verify_narrow
    import json
    import time
    out = {'comparison_with_verify_narrow': []}
    for rows, cols in [(5, m) for m in range(3, 26)] + [(5, 40), (5, 60), (6, 6), (7, 7), (8, 8)]:
        t = time.time()
        mine = rectangles_by_sides(rows, cols)
        theirs = verify_narrow.rectangles(rows, cols)
        same = mine == theirs
        out['comparison_with_verify_narrow'].append(
            {'rows': rows, 'cols': cols, 'rectangles': len(mine), 'equal_sets': same,
             'seconds': round(time.time() - t, 2)})
        assert same, (rows, cols)
    out['squares_A085582'] = {n: len(rectangles_by_sides(n, n)) for n in range(2, 9)}
    os.makedirs(os.path.join(HERE, '..', 'data'), exist_ok=True)
    with open(os.path.join(HERE, '..', 'data', 'five_row_geometry_check.json'), 'w') as f:
        json.dump(out, f, indent=1)
    print(json.dumps(out['squares_A085582']))
    print('rectangle lists agree with verify_narrow on all', len(out['comparison_with_verify_narrow']), 'grids')


if __name__ == '__main__':
    main()
