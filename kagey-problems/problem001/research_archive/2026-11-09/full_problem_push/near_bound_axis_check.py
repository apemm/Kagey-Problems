"""Finite checks of the individual-completion structural inequalities.

Singleton and empty columns do not affect the row graph, so the exhaustive
part enumerates distinct column sets of size at least two.
"""
from itertools import combinations, product
from pathlib import Path
import json
import time


HERE = Path(__file__).resolve().parent


def q(h):
    return h * h // 4


def axis_valid(h, columns):
    owners = {}
    for i, column in enumerate(columns):
        for pair in combinations(column, 2):
            if pair in owners:
                return False
            owners[pair] = i
    for a, b, c in combinations(range(h), 3):
        labels = (owners.get((a, b)), owners.get((a, c)), owners.get((b, c)))
        if None not in labels and len(set(labels)) == 3:
            return False
    return True


def bipartite(h, edges):
    neighbors = [[] for _ in range(h)]
    for a, b in edges:
        neighbors[a].append(b)
        neighbors[b].append(a)
    colors = {}
    for start in range(h):
        if start in colors:
            continue
        colors[start] = 0
        stack = [start]
        while stack:
            a = stack.pop()
            for b in neighbors[a]:
                if b not in colors:
                    colors[b] = 1 - colors[a]
                    stack.append(b)
                elif colors[b] == colors[a]:
                    return False
    return True


def exhaustive_families(h, limit=4):
    possible = [c for size in range(2, h + 1)
                for c in combinations(range(h), size)]
    checked = 0
    for size in range(limit + 1):
        for columns in combinations(possible, size):
            if not axis_valid(h, columns):
                continue
            checked += 1
            excess = sum(len(c) - 1 for c in columns)
            assert excess <= q(h)
            for column in columns:
                assert excess <= h - 1 + q(h - len(column))
            if q(h) - excess < h // 2 - 1:
                assert all(len(c) == 2 for c in columns)
                assert bipartite(h, columns)
    return {"height": h, "max_nonsingleton_columns": limit,
            "valid_column_families_checked": checked}


def sharpness(h):
    remaining = list(range(3, h))
    a = remaining[:len(remaining) // 2]
    c = remaining[len(remaining) // 2:]
    columns = [(0, 1, 2)]
    columns += [(0, x) for x in a]
    columns += [(1, x) for x in c]
    columns += [(x, y) for x in a for y in c]
    columns = [tuple(sorted(column)) for column in columns]
    assert axis_valid(h, columns)
    m = q(h) - h // 2
    assert len(columns) == m
    assert sum(map(len, columns)) == 2 * m + 1
    return {"height": h, "columns": m, "black_points": 2 * m + 1}


def seven_by_nine_patterns():
    count = 0
    for b in combinations(range(7), 3):
        outside = tuple(x for x in range(7) if x not in b)
        # Fix the first outside vertex in the first side to avoid swapping.
        for second in outside[1:]:
            a = (outside[0], second)
            c = tuple(x for x in outside if x not in a)
            edges = [(x, y) for x in a for y in c]
            for colors in product(b, repeat=4):
                attach = dict(zip(outside, colors))
                if any(attach[x] == attach[y] for x, y in edges):
                    continue
                columns = [b] + edges + [(x, attach[x]) for x in outside]
                columns = tuple(tuple(sorted(column)) for column in columns)
                assert axis_valid(7, columns)
                assert len(columns) == 9 and sum(map(len, columns)) == 19
                count += 1
    assert count == 1890
    return count


def main():
    started = time.monotonic()
    families = [exhaustive_families(h) for h in range(3, 7)]
    sharp = [sharpness(h) for h in range(5, 31)]
    patterns = seven_by_nine_patterns()
    out = {"exhaustive_families": families,
           "sharpness_examples": sharp,
           "seven_by_nine_axis_patterns": patterns,
           "elapsed_seconds": time.monotonic() - started}
    (HERE / "near_bound_axis_checks.json").write_text(
        json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(out), flush=True)


if __name__ == "__main__":
    main()
