"""Rectangle enumeration. OWNER: Arjun.

rectangles(rows, cols) -> list[frozenset[tuple[int, int]]]
    All rectangles with four corners on grid points, tilted included, degenerates excluded,
    deduplicated. Points are (i, j) = (column, row), 1-indexed (PROBLEM.md convention 1).

Method (constructive; independent of the 4-subset test in brute.py): choose an ordered
side p -> q with direction v = q - p != 0, and a perpendicular offset w = t * (-v_y, v_x)/g
for integer t >= 1, where g = gcd(|v_x|, |v_y|) so that (-v_y, v_x)/g is the primitive
perpendicular lattice vector. The four corners p, q, q + w, p + w are a nondegenerate
rectangle; every lattice rectangle arises this way (several times), so we dedupe by
frozenset of corners.

Validation gate: hand-checked counts are 2x3 -> 3, 3x3 -> 10 (9 axis-aligned + 1 tilted
unit diamond), 3x4 -> 20 (18 + 2). See tests/test_fixtures.py::test_rectangle_counts.
"""
from math import gcd


def grid_points(rows, cols):
    """All (i, j) with 1 <= i <= cols, 1 <= j <= rows, column-major to match brute.py."""
    return [(i, j) for i in range(1, cols + 1) for j in range(1, rows + 1)]


def rectangles(rows, cols):
    pts = grid_points(rows, cols)
    inside = set(pts)
    found = set()
    for p in pts:
        for q in pts:
            vx, vy = q[0] - p[0], q[1] - p[1]
            if (vx, vy) == (0, 0):
                continue
            g = gcd(abs(vx), abs(vy))
            ux, uy = -vy // g, vx // g          # primitive perpendicular
            t = 1
            while True:
                w = (t * ux, t * uy)
                r = (q[0] + w[0], q[1] + w[1])
                s = (p[0] + w[0], p[1] + w[1])
                if r not in inside or s not in inside:
                    # Moving further along w only leaves the grid faster: coordinates are
                    # monotone in t, so once either corner exits it never re-enters.
                    if (r[0] < 1 or r[0] > cols or r[1] < 1 or r[1] > rows or
                            s[0] < 1 or s[0] > cols or s[1] < 1 or s[1] > rows):
                        break
                found.add(frozenset((p, q, r, s)))
                t += 1
    return sorted(found, key=lambda R: sorted(R))
