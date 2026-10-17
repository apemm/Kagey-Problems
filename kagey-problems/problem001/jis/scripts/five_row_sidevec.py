"""A rectangle enumerator by corner and perpendicular side vectors, used as a second source of
rectangles next to verify_narrow.rectangles (equal diagonals with a common midpoint).

A rectangle is p, p+u, p+v, p+u+v with u, v non-zero integer vectors, u.v = 0, all four corners
on the grid. Zero-based (column, row) inside; masks use bit row*cols + column, the convention of
verify_narrow.py, so the two enumerators can be compared as sorted mask lists.
"""
from math import gcd


def rectangles_sidevec(rows, cols):
    found = set()
    for x in range(cols):
        for y in range(rows):
            for a in range(-cols + 1, cols):
                for b in range(-rows + 1, rows):
                    if a == 0 and b == 0:
                        continue
                    if not (0 <= x + a < cols and 0 <= y + b < rows):
                        continue
                    g = gcd(abs(a), abs(b))
                    pa, pb = -b // g, a // g          # primitive perpendicular direction
                    k = 1
                    while True:
                        va, vb = k * pa, k * pb
                        if not (0 <= x + va < cols and 0 <= y + vb < rows):
                            # k larger only moves further out in the same direction
                            break
                        if 0 <= x + a + va < cols and 0 <= y + b + vb < rows:
                            pts = ((x, y), (x + a, y + b), (x + va, y + vb), (x + a + va, y + b + vb))
                            found.add(sum(1 << (q * cols + p) for p, q in pts))
                        k += 1
                    k = -1
                    while True:
                        va, vb = k * pa, k * pb
                        if not (0 <= x + va < cols and 0 <= y + vb < rows):
                            break
                        if 0 <= x + a + va < cols and 0 <= y + b + vb < rows:
                            pts = ((x, y), (x + a, y + b), (x + va, y + vb), (x + a + va, y + b + vb))
                            found.add(sum(1 << (q * cols + p) for p, q in pts))
                        k -= 1
    return sorted(found)


def presentations_injective(rects, black):
    """Validity from the definition: the map rectangle -> visible corners is injective."""
    seen = {}
    for r in rects:
        vis = r & ~black
        if vis in seen:
            return False, (seen[vis], r)
        seen[vis] = r
    return True, None
