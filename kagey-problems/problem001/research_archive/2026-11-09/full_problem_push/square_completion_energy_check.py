"""Independent exact checks for the six-point paraboloid counterexample."""
from collections import defaultdict
from itertools import combinations, product
from pathlib import Path
import json


def norm(p):
    return p[0] ** 2 + p[1] ** 2


def sub(a, b):
    return a[0] - b[0], a[1] - b[1]


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1]


def main():
    points = [(1, 0), (2, 5), (-3, -5), (0, 1), (-5, 2), (5, -3)]
    lifts = [(x, y, x * x + y * y) for x, y in points]
    left = tuple(sum(p[j] for p in lifts[:3]) for j in range(3))
    right = tuple(sum(p[j] for p in lifts[3:]) for j in range(3))
    assert left == right == (0, 0, 64)
    right_angles = []
    for b in points:
        for a, c in combinations([p for p in points if p != b], 2):
            if dot(sub(a, b), sub(c, b)) == 0:
                right_angles.append((a, b, c))
    assert not right_angles
    pairs_by_norm = defaultdict(list)
    for a, b in combinations(points, 2):
        pairs_by_norm[norm(sub(a, b))].append((a, b))
    repeated = []
    for squared_length, pairs in pairs_by_norm.items():
        for (a, b), (c, d) in combinations(pairs, 2):
            H = (c[0] + d[0] - a[0] - b[0], c[1] + d[1] - a[1] - b[1])
            dots = [dot(H, sub(b, a)), dot(H, sub(d, c))]
            assert all(dots)
            repeated.append({"squared_length": squared_length, "dot_products": dots})

    # Enumerate rectangles from equal-length diagonals, independently of the
    # research solver and of the pointwise completion formulation.
    black = {(x + 5, y + 5) for x, y in points}
    diagonals = defaultdict(list)
    for a, b in combinations(product(range(11), repeat=2), 2):
        diagonals[(a[0] + b[0], a[1] + b[1], norm(sub(a, b)))].append((a, b))
    presentations = {}
    rectangles = 0
    for pairs in diagonals.values():
        for ab, cd in combinations(pairs, 2):
            rectangle = frozenset(ab + cd)
            assert len(rectangle) == 4
            white = rectangle - black
            assert white not in presentations
            presentations[white] = rectangle
            rectangles += 1
    result = {
        "status": "passed",
        "common_three_lift_sum": left,
        "black_right_angles": len(right_angles),
        "equal_length_pair_checks": repeated,
        "independently_enumerated_rectangles_on_11_by_11": rectangles,
        "presentation_collisions": 0,
    }
    Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
