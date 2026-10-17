"""Shared pieces for the independent width-21 checks of the five-row results.

Everything here is written from the definitions, not from the other scripts in this folder:
rectangles are generated from right-angle triples (a corner p and two further grid points q, r
with (q - p) . (r - p) = 0 whose fourth corner q + r - p lies on the grid), and a blackout is
valid when the map rectangle -> visible corners is injective over all rectangles.

Coordinates inside this module are zero-based (x = column, y = row), (0, 0) top left; the
helpers one_based / zero_based translate to and from the one-based (column, row) convention of
verify_narrow.py and of every JSON file written by the check scripts.
"""
from itertools import combinations

# the published width-21 witness, one-based (column, row)
WITNESS_21 = [(1, 1), (1, 2), (2, 1), (3, 1), (4, 1), (5, 1), (5, 4), (6, 1), (7, 1), (8, 1),
              (9, 2), (9, 3), (10, 1), (11, 1), (12, 1), (13, 3), (13, 4), (14, 1), (15, 1),
              (16, 1), (17, 2), (17, 5), (18, 1), (19, 1), (20, 1), (21, 4), (21, 5)]


def one_based(points):
    return sorted((x + 1, y + 1) for x, y in points)


def zero_based(points):
    return sorted((c - 1, r - 1) for c, r in points)


def rectangles(rows, cols):
    """All rectangles with corners on the rows x cols grid, as frozensets of (x, y)."""
    points = [(x, y) for y in range(rows) for x in range(cols)]
    on_grid = set(points)
    found = set()
    for px, py in points:
        others = [(qx - px, qy - py) for qx, qy in points if (qx, qy) != (px, py)]
        for (ux, uy), (vx, vy) in combinations(others, 2):
            if ux * vx + uy * vy != 0:
                continue
            sx, sy = px + ux + vx, py + uy + vy
            if (sx, sy) in on_grid:
                found.add(frozenset(((px, py), (px + ux, py + uy), (px + vx, py + vy), (sx, sy))))
    return sorted(found, key=sorted)


def is_axis(rect):
    xs = {x for x, _ in rect}
    return len(xs) == 2


def presentation_collision(rects, black):
    """None if the visible-corner map is injective, else a pair of rectangles that present alike."""
    black = set(black)
    seen = {}
    for rect in rects:
        visible = frozenset(p for p in rect if p not in black)
        if visible in seen:
            return seen[visible], rect
        seen[visible] = rect
    return None


def is_valid(rects, black):
    return presentation_collision(rects, black) is None


def klein_images(points, rows, cols):
    """The four images of a point set under the Klein group: identity, row reflection,
    column reversal, half turn (zero-based)."""
    maps = (lambda x, y: (x, y), lambda x, y: (x, rows - 1 - y),
            lambda x, y: (cols - 1 - x, y), lambda x, y: (cols - 1 - x, rows - 1 - y))
    return [frozenset(f(x, y) for x, y in points) for f in maps]


def column_profile(points, cols):
    """Row sets per column, zero-based."""
    prof = [set() for _ in range(cols)]
    for x, y in points:
        prof[x].add(y)
    return prof


def equality_shape(points, rows, cols):
    """Return (two_rows, three_rows, double_columns, singleton_rows) if the point set has the
    equality structure (every column one or two black, the doubles the edges of a balanced
    complete bipartite graph on the rows, each edge once), else None. Zero-based."""
    prof = column_profile(points, cols)
    doubles = [(x, tuple(sorted(s))) for x, s in enumerate(prof) if len(s) == 2]
    if any(len(s) not in (1, 2) for s in prof):
        return None
    edges = [e for _, e in doubles]
    if len(set(edges)) != len(edges):
        return None
    half = rows // 2
    for side in combinations(range(rows), half):
        other = tuple(r for r in range(rows) if r not in side)
        need = {tuple(sorted((a, b))) for a in side for b in other}
        if need == set(edges):
            singles = sorted({next(iter(s)) for s in prof if len(s) == 1})
            return side, other, [x for x, _ in doubles], singles
    return None
