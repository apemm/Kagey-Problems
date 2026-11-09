"""Exact checks for the CRT double placements in quadratic_arithmetic.md."""

from collections import defaultdict
from math import gcd, isqrt
import json
import time


def prime_after(n):
    n += 1
    while any(n % d == 0 for d in range(2, isqrt(n) + 1)):
        n += 1
    return n


def placement(h, strong=False):
    if strong:
        scale = 1
        while scale * scale <= 4 * h:
            scale *= 2
        p = prime_after(scale * scale + 4)
        q = prime_after(2 * (scale * scale + 4))
    else:
        scale = 4
        p = prime_after(10 * h)
        q = prime_after(2 * 10 * h)
    inverse = pow(p, -1, q)
    edges = []
    for a in range((h + 1) // 2):
        for b in range(h // 2):
            x = a + p * (((b - a) * inverse) % q)
            edges.append((scale * x, 2 * a + 1, 2 * b + 2))
    points = [(x, r) for x, a, b in edges for r in (a, b)]
    return scale, p, q, edges, points


def direction(x, y):
    g = gcd(abs(x), abs(y))
    x, y = x // g, y // g
    return (x, y) if x > 0 or (x == 0 and y > 0) else (-x, -y)


def right_angles(points):
    for vertex in points:
        directions = {}
        for point in points:
            dx, dy = point[0] - vertex[0], point[1] - vertex[1]
            if dx == 0 or dy == 0:
                continue
            key = direction(dx, dy)
            perpendicular = direction(-dy, dx)
            if perpendicular in directions:
                return vertex, point, directions[perpendicular]
            directions[key] = point
    return None


def vertical_p(h, points):
    for i, a in enumerate(points):
        for c in points[i + 1:]:
            dx, dy = c[0] - a[0], c[1] - a[1]
            if not dx or dy % 2 == 0:
                continue
            norm = dx * dx + dy * dy
            length = isqrt(norm)
            if length * length != norm:
                continue
            lower, upper = (a[1] + c[1] - length) // 2, (a[1] + c[1] + length) // 2
            if 1 <= lower < upper <= h:
                return a, c, ((a[0] + c[0]) // 2, lower), ((a[0] + c[0]) // 2, upper)
    return None


def mixed_system(points, oblique_side=True, in_height=None):
    """Check the actual four-point equations, without CRT shortcuts.

    The default omits axis sides. With oblique_side=False, horizontal and
    vertical sides are also checked, including horizontal axis rivals.
    With no in_height, a returned certificate need not stay in the strip.
    """
    by_norm = defaultdict(list)
    for i, a in enumerate(points):
        for j in range(i + 1, len(points)):
            b = points[j]
            dx, dy = b[0] - a[0], b[1] - a[1]
            by_norm[dx * dx + dy * dy].append((i, j, dx, dy))
    for pairs in by_norm.values():
        for i, j, ux, uy in pairs:
            if oblique_side and (not ux or not uy):
                continue
            a, b = points[i], points[j]
            for k, l, vx, vy in pairs:
                if len({i, j, k, l}) != 4:
                    continue
                if (vx, vy) in ((ux, uy), (-ux, -uy)):
                    continue
                c, d = points[k], points[l]
                mx, my = a[0] + b[0] - c[0] - d[0], a[1] + b[1] - c[1] - d[1]
                if (mx or my) and mx * ux + my * uy == 0:
                    # Only integer white corners can define lattice rectangles.
                    if (c[0] + d[0] - ux) % 2 or (c[1] + d[1] - uy) % 2:
                        continue
                    if in_height is not None:
                        wy = (c[1] + d[1] - uy) // 2
                        zy = (c[1] + d[1] + uy) // 2
                        if not (1 <= min(wy, zy) <= max(wy, zy) <= in_height):
                            continue
                    return a, b, c, d
    return None


def main():
    started = time.monotonic()
    rows = []
    for h in range(3, 32):
        scale, p, q, edges, points = placement(h)
        assert len({x for x, _, _ in edges}) == len(edges)
        assert right_angles(points) is None, h
        rows.append({"height": h, "scale": scale, "p": p, "q": q, "points": len(points), "right_angles": 0})
    p_witness = vertical_p(7, placement(7)[4])
    assert p_witness is not None
    strong_rows = []
    for h in range(3, 26):
        scale, p, q, edges, points = placement(h, True)
        assert right_angles(points) is None, h
        assert vertical_p(h, points) is None, h
        assert mixed_system(points) is None, h
        assert mixed_system(points, False, h) is None, h
        strong_rows.append({"height": h, "scale": scale, "p": p, "q": q, "points": len(points), "oblique_mixed": 0, "vertical_p": 0})
    print(json.dumps({"quadratic_right_angle_checks": rows, "quadratic_p_counterexample_h7": p_witness,
                      "strong_checks": strong_rows, "seconds": time.monotonic() - started}, indent=2))


if __name__ == "__main__":
    main()
