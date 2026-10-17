"""Shared pieces for the independent checks of the small-cell and six-row results.

Rectangles are generated from right-angle corner triples: for a corner B and a
second corner A, the third corner C runs over the lattice points on the line
through B perpendicular to BA, and D = A + C - B closes the rectangle.  This is a
different route from the equal-diagonal enumerator of verify_narrow.py and from
the side-vector enumerator of the jis scripts.

Coordinates are one-based (column, row) with (1,1) top left throughout; nothing
here is zero-based.
"""
from math import gcd


def grid_points(rows, cols):
    return [(c, r) for r in range(1, rows + 1) for c in range(1, cols + 1)]


def rectangles_by_triples(rows, cols):
    """All non-degenerate rectangles with corners on the rows x cols grid, as a
    sorted list of 4-tuples of one-based (column, row) corners."""
    found = set()
    inside = lambda c, r: 1 <= c <= cols and 1 <= r <= rows
    for bc in range(1, cols + 1):
        for br in range(1, rows + 1):
            for ac in range(1, cols + 1):
                for ar in range(1, rows + 1):
                    vx, vy = ac - bc, ar - br
                    if vx == 0 and vy == 0:
                        continue
                    # primitive perpendicular direction
                    g = gcd(abs(vx), abs(vy))
                    px, py = -vy // g, vx // g
                    t = 1
                    while True:
                        cc, cr = bc + t * px, br + t * py
                        if not inside(cc, cr):
                            break
                        dc, dr = ac + t * px, ar + t * py
                        if inside(dc, dr):
                            found.add(tuple(sorted(((ac, ar), (bc, br), (cc, cr), (dc, dr)))))
                        t += 1
                    t = -1
                    while True:
                        cc, cr = bc + t * px, br + t * py
                        if not inside(cc, cr):
                            break
                        dc, dr = ac + t * px, ar + t * py
                        if inside(dc, dr):
                            found.add(tuple(sorted(((ac, ar), (bc, br), (cc, cr), (dc, dr)))))
                        t -= 1
    return sorted(found)


def first_collision(rects, black):
    """Return None if every rectangle has a distinct visible presentation under the
    blackout `black` (a set of one-based points), else a colliding pair."""
    black = set(black)
    seen = {}
    for rect in rects:
        visible = frozenset(p for p in rect if p not in black)
        if visible in seen:
            return seen[visible], rect
        seen[visible] = rect
    return None


def is_valid(rects, black):
    return first_collision(rects, black) is None


def picture(points, rows, cols):
    black = set(map(tuple, points))
    return ['' .join('#' if (c, r) in black else '.' for c in range(1, cols + 1))
            for r in range(1, rows + 1)]


def axis_counts(rects):
    axis = sum(1 for rect in rects if len({c for c, _ in rect}) == 2)
    return axis, len(rects) - axis
