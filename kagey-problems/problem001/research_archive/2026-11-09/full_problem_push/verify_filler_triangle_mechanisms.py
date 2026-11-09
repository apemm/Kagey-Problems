"""Exact checks for safe triangles and the universal-column obstruction."""
import itertools
import json
from collections import defaultdict
from pathlib import Path


def rectangle(points):
    points = tuple(points)
    if len(set(points)) != 4:
        return False
    for i in (1, 2, 3):
        a, c = points[0], points[i]
        b, d = [points[j] for j in range(4) if j not in (0, i)]
        if (a[0] + c[0], a[1] + c[1]) != (b[0] + d[0], b[1] + d[1]):
            continue
        if sum((a[k] - c[k]) ** 2 for k in (0, 1)) == sum((b[k] - d[k]) ** 2 for k in (0, 1)):
            return True
    return False


def complete(h, part, core):
    other = set(range(1, h + 1)) - part
    all_edges = {tuple(sorted((a, b))) for a in part for b in other}
    core = {x: tuple(sorted(edge)) for x, edge in core.items()}
    assert len(set(core.values())) == len(core)
    assert set(core.values()) <= all_edges
    remaining = iter(sorted(all_edges - set(core.values())))
    result = dict(core)
    for x in range(len(all_edges)):
        if x not in result:
            result[x] = next(remaining)
    assert set(result.values()) == all_edges
    return result


def test_universal_assignments():
    cases = 0
    for h in (10, 11):
        for raw in itertools.combinations(range(1, h + 1), h // 2):
            part = set(raw)
            if h % 2 == 0 and 1 not in part:
                continue
            def opposite(row):
                return (set(range(1, h + 1)) - part) if row in part else part
            for d in range(1, (h - 1) // 2 + 1):
                r, s, w = 1, 1 + d, 1 + 2 * d
                selected = {r, s, w}
                root_mate = min(opposite(r) - selected)
                outer_mates = sorted(opposite(s) - selected)[:2]
                assert len(outer_mates) == 2
                cols = complete(h, part, {d: (r, root_mate),
                                         0: (s, outer_mates[0]),
                                         2 * d: (s, outer_mates[1])})
                black = {(x, y) for x, ys in cols.items() for y in ys}
                W = (d, w)
                assert W not in black
                z = next(y for y in cols[d] if (y in part) != (w in part))
                owner = next(x for x, ys in cols.items() if set(ys) == {w, z})
                R = {(d, r), (0, s), (2 * d, s), W}
                T = {W, (d, z), (owner, w), (owner, z)}
                assert rectangle(R) and rectangle(T) and R != T
                assert R - black == T - black == {W}
                cases += 1
            for u in range(1, h):
                for v in range(u + 1, h - u):
                    rows = {1, 1 + u, 1 + v, 1 + u + v}
                    points = [(0, 1 + v), (u, 1 + u + v),
                              (v, 1), (u + v, 1 + u)]
                    core = {x: (y, min(opposite(y) - rows)) for x, y in points}
                    cols = complete(h, part, core)
                    black = {(x, y) for x, ys in cols.items() for y in ys}
                    A, B, C, D = points
                    P, Q = (0, 1 + u), (u + v, 1 + v)
                    R, T = {A, D, P, Q}, {B, C, P, Q}
                    assert rectangle(R) and rectangle(T) and R != T
                    assert R ^ T == set(points)
                    assert R - black == T - black == {P, Q}
                    cases += 1
    return cases


def test_seven_board():
    cols = [(1, 6), (3, 6), (5,), (2, 5), (2,), (2,), (1, 4),
            (7,), (1, 2), (2, 7), (2,), (7,), (6, 7), (7,),
            (4, 7), (7,), (7,), (5, 6), (4, 5), (3, 4), (2, 3)]
    black = {(x, y) for x, ys in enumerate(cols) for y in ys}
    inserted = {(x, y) for x, ys in enumerate(cols) if len(ys) == 2 for y in ys}
    assert len(black) == 33
    assert {tuple(sorted(ys)) for ys in cols if len(ys) == 2} == {
        tuple(sorted((a, b))) for a in (1, 3, 5, 7) for b in (2, 4, 6)}
    vertices = [(x, y) for x in range(21) for y in range(1, 8)]
    diagonals = defaultdict(list)
    for a, b in itertools.combinations(vertices, 2):
        norm = sum((a[k] - b[k]) ** 2 for k in (0, 1))
        diagonals[(a[0] + b[0], a[1] + b[1], norm)].append((a, b))
    seen = {}
    safe = []
    for pairs in diagonals.values():
        for d1, d2 in itertools.combinations(pairs, 2):
            R = frozenset(d1 + d2)
            assert len(R) == 4
            W = frozenset(R - black)
            assert W not in seen or seen[W] == R, (seen.get(W), R, W)
            seen[W] = R
            if len(R & inserted) == 3:
                missing = next(iter(R - inserted))
                # An axis rectangle can use three double cells, so retain tilted ones only.
                if len({x for x, y in R}) == 2 and len({y for x, y in R}) == 2:
                    continue
                assert len(cols[missing[0]]) == 1
                filler = cols[missing[0]][0]
                assert filler != missing[1] and filler % 2 == missing[1] % 2
                safe.append({"black": sorted(R & inserted), "completion": missing,
                             "filler": (missing[0], filler)})
    assert len(safe) == 2
    return {"rectangles": len(seen), "black_cells": len(black),
            "safe_inserted_triangles": safe}


def test_two_obstructions():
    odd = {(0, 3), (1, 5), (4, 1), (5, 3)}
    even = {(x, y + 1) for x, y in odd}
    assert rectangle(odd) and rectangle(even)
    W = (0, 5)
    R = {W, (1, 7), (4, 3), (5, 5)}
    T = {W, (2, 9), (8, 1), (10, 5)}
    assert rectangle(R) and rectangle(T) and R & T == {W}
    return {"opposite_completion_rows": [3, 4], "duplicate_completion": W}


def main():
    result = {"status": "PASS", "seven_board": test_seven_board(),
              "arbitrary_partition_certificates": test_universal_assignments(),
              "local_obstructions": test_two_obstructions()}
    Path(__file__).with_name("filler_triangle_mechanisms_check.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
