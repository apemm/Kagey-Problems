"""Finite checks of the square obstruction codegrees and sampling exponents.

The asymptotic results are proved in square_progress.md. This script uses
standard-library integer arithmetic and does not assume those results.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path
import time


HERE = Path(__file__).resolve().parent


def rectangle_family(n):
    points = tuple((x, y) for x in range(n) for y in range(n))
    rectangles = set()
    for triple in combinations(points, 3):
        for i in range(3):
            b = triple[i]
            a, c = (triple[j] for j in range(3) if j != i)
            u = (a[0] - b[0], a[1] - b[1])
            v = (c[0] - b[0], c[1] - b[1])
            if u[0] * v[0] + u[1] * v[1]:
                continue
            x = (a[0] + c[0] - b[0], a[1] + c[1] - b[1])
            if 0 <= x[0] < n and 0 <= x[1] < n:
                rectangle = frozenset((*triple, x))
                assert len(rectangle) == 4
                rectangles.add(rectangle)
    return rectangles


def check(n):
    rectangles = rectangle_family(n)
    vertex_degrees = Counter(p for r in rectangles for p in r)
    pair_degrees = Counter(pair for r in rectangles
                           for pair in combinations(sorted(r), 2))
    d = max(vertex_degrees.values(), default=0)
    m = max(pair_degrees.values(), default=0)
    assert m <= 6 * n
    six_edges = {r ^ s for r, s in combinations(rectangles, 2)
                 if len(r & s) == 1}
    assert all(len(e) == 6 for e in six_edges)
    upper = (3 * d * d, 5 * m * d, d + 6 * m * m, 10 * m, 10)
    observed = []
    for j in range(1, 6):
        counts = Counter(t for edge in six_edges
                         for t in combinations(sorted(edge), j))
        maximum = max(counts.values(), default=0)
        assert maximum <= upper[j - 1], (n, j, maximum, upper[j - 1])
        observed.append(maximum)
    expected_rectangles = {2: 1, 3: 10, 4: 44, 5: 130, 6: 313}
    assert len(rectangles) == expected_rectangles[n]
    return {"side": n, "rectangles": len(rectangles),
            "six_edges": len(six_edges), "D": d, "M": m,
            "max_codegrees_1_to_5": observed,
            "proved_bounds_1_to_5": upper}


def main():
    started = time.monotonic()
    a = Fraction(79, 100)
    ratios = {
        "four_edges": Fraction(21, 10) - 3 * a,
        "overlap_2": 7 - 9 * a,
        "overlap_3": 6 - 8 * a,
        "overlap_4": 5 - 7 * a,
        "overlap_5": 4 - 6 * a,
    }
    assert all(e < 0 for e in ratios.values())
    average_degree_power = 4 - 5 * a
    retained_size_power = (2 - a) - average_degree_power / 5
    assert average_degree_power == Fraction(1, 20)
    assert retained_size_power == Fraction(6, 5)
    cases = []
    for n in range(2, 7):
        result = check(n)
        cases.append(result)
        print(json.dumps(result), flush=True)
    out = {"cases": cases,
           "deletion_ratios_power_of_n": {k: str(v) for k, v in ratios.items()},
           "average_degree_power": str(average_degree_power),
           "final_size_power": str(retained_size_power),
           "elapsed_seconds": time.monotonic() - started}
    (HERE / "square_codegree_checks.json").write_text(
        json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print("All finite checks passed.", flush=True)


if __name__ == "__main__":
    main()
