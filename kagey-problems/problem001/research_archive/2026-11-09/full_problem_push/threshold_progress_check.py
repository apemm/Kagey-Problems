"""Construct and directly check the even-height threshold argument.

Standard-library only. The final check hashes actual tilted presentations and
tests their full parity-axis rivals; it does not reuse the forbidden-shift test.
"""

from collections import defaultdict
from itertools import combinations, product
from math import isqrt
from pathlib import Path
import json
import random
import time


def divisors(n):
    out = []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            out.append(d)
            if d * d != n:
                out.append(n // d)
    return out


def tilts(h):
    out = set()
    for b in range(1, h):
        for d in range(1, h - b):
            for a in divisors(b * d):
                c = b * d // a
                for r in range(1, h - b - d + 1):
                    out.add(tuple(sorted(((0, r + b), (a, r),
                                          (c, r + b + d), (a + c, r + d)))))
    return tuple(sorted(out))


def mixed_supports(h):
    out = set()
    for a, b, c, d in product(range(1, h + 1), repeat=4):
        y, v, s = b - a, d - c, a + b - c - d
        candidates = []
        if y:
            if not s:
                continue
            for x in divisors(abs(s * y)):
                q = x * x + y * y - v * v
                if q < 0 or isqrt(q) ** 2 != q:
                    continue
                for z in {isqrt(q), -isqrt(q)}:
                    candidates.append((x, z, -s * y // x))
        elif v and s:
            for f in divisors(v * v):
                g = v * v // f
                if (f + g) % 2:
                    continue
                candidates.append(((f + g) // 2, (g - f) // 2, 0))
        for x, z, hx in candidates:
            if hx % 2 or (x - hx - z) % 2 or (c + d - y) % 2:
                continue
            if (z, v) in ((x, y), (-x, -y)):
                continue
            A, B = (0, a), (x, b)
            C, D = ((x - hx - z) // 2, c), ((x - hx + z) // 2, d)
            W, Z = (-hx // 2, (c + d - y) // 2), (x - hx // 2, (c + d + y) // 2)
            if not (1 <= W[1] <= h and 1 <= Z[1] <= h):
                continue
            if len({A, B, C, D, W, Z}) != 6:
                continue
            assert x * hx + s * y == 0
            assert x * x + y * y == z * z + v * v
            low = min(A[0], B[0], C[0], D[0])
            out.add(tuple(sorted((u - low, r) for u, r in (A, B, C, D))))
    return tuple(sorted(out))


def grouped(points):
    out = defaultdict(set)
    for x, r in points:
        out[x].add(r)
    return dict(out)


def build(h, seed, selected_edges=None, sea_top=None):
    g = h if sea_top is None else sea_top
    edges = ([frozenset((a, b)) for a in range(1, h + 1, 2)
              for b in range(2, h + 1, 2)]
             if selected_edges is None else selected_edges)
    if not edges:
        return [], [], [], 0, 0
    rectangles = tilts(h)
    mixed = mixed_supports(h)
    row_diffs = defaultdict(set)
    for R in rectangles:
        for (x, r), (z, s) in combinations(R, 2):
            if x != z:
                row_diffs[r, s].add(z - x)
                row_diffs[s, r].add(x - z)
    hypers = set()
    for d in range(1, h):
        for f in divisors(d * d):
            other_factor = d * d // f
            if (f + other_factor) % 2 == 0:
                hypers.add((f + other_factor) // 2)
                hypers.add(-(f + other_factor) // 2)

    supports = list(mixed)
    supports += [tuple(sorted(T)) for R in rectangles for T in combinations(R, 3)]
    influence = []
    boundary = {1, g}
    for e in edges:
        offsets = set()
        for S in supports:
            cols = grouped(S)
            for center, rows in cols.items():
                if not rows <= e:
                    continue
                if all(len(rs) == 1 and rs <= boundary
                       for x, rs in cols.items() if x != center):
                    offsets.update(x - center for x in cols if x != center)
        influence.append(offsets)

    mixed_diffs = defaultdict(set)
    for S in mixed:
        cols = grouped(S)
        for x, z in product(cols, repeat=2):
            if x == z:
                continue
            if not all(len(rs) == 1 and rs <= boundary
                       for u, rs in cols.items() if u not in (x, z)):
                continue
            left = [i for i, e in enumerate(edges) if cols[x] <= e]
            right = [j for j, e in enumerate(edges) if cols[z] <= e]
            for i, j in product(left, right):
                if i != j:
                    mixed_diffs[i, j].add(z - x)

    centers = []
    for j, e in enumerate(edges):
        excluded = set()
        for i, f in enumerate(edges[:j]):
            shifts = set(hypers)
            shifts.update(mixed_diffs[i, j])
            for r, s in product(f, e):
                shifts.update(row_diffs[r, s])
            shifts.update(a - b for a in influence[i] | {0}
                          for b in influence[j] | {0})
            excluded.update(centers[i] + d for d in shifts)
        center = 0
        while center in excluded:
            center += 1
        centers.append(center)

    W = 1 + (h - 1) ** 2 // 4
    low, high = min(centers) - 2 * W, max(centers) + 2 * W
    rng = random.Random(seed)
    columns = [frozenset((rng.choice((1, g)),)) for _ in range(high - low + 1)]
    assigned = set()
    for e, c, offsets in zip(edges, centers, influence):
        for d in offsets | {0}:
            assert c + d not in assigned
            assigned.add(c + d)
            columns[c + d - low] = e if d == 0 else frozenset((1 if d < 0 else g,))
    return columns, centers, influence, len(rectangles), len(mixed)


def check(h, columns):
    # Exhaustively hash actual white presentations of every tilted rectangle.
    seen = {}
    tested = weak = 0
    for R in tilts(h):
        span = max(x for x, _ in R)
        for shift in range(len(columns) - span):
            corners = tuple((x + shift, r) for x, r in R)
            white = tuple(p for p in corners if p[1] not in columns[p[0]])
            tested += 1
            if len(white) > 2:
                continue
            weak += 1
            assert len(white) == 2, (h, "three black", corners, white)
            assert white not in seen, (h, "tilt collision", corners, seen.get(white))
            seen[white] = corners
            (x, r), (z, s) = white
            if x == z:
                rival = (r - s) % 2
            elif r == s:
                rival = bool(columns[x] & columns[z])
            else:
                rival = s in columns[x] and r in columns[z]
            assert not rival, (h, "axis rival", corners, white)
    doubles = [c for c in columns if len(c) == 2]
    assert len(doubles) == h * h // 4 and len(set(doubles)) == len(doubles)
    assert all(sum(c) % 2 for c in doubles)
    assert sum(map(len, columns)) == len(columns) + h * h // 4
    return tested, weak


def main():
    start = time.perf_counter()
    results = []
    for h in (4, 6, 8, 10):
        for seed in range(3):
            columns, centers, influence, templates, mixed = build(h, seed)
            tested, weak = check(h, columns)
            results.append({"height": h, "seed": seed, "width": len(columns),
                            "black_cells": sum(map(len, columns)),
                            "double_centers": centers,
                            "max_influence_size": max(map(len, influence)),
                            "tilted_templates": templates, "mixed_supports": mixed,
                            "rectangles_checked": tested, "weak_presentations": weak})
    odd_results = []
    for h in (5, 7, 9, 11):
        L = 2 * (1 + (h - 1) ** 2 // 4)
        exceptional = {h} | {h - 4 * j * j for j in range(1, isqrt(h) + 1)
                            if h - 4 * j * j >= 3}
        edges = [frozenset((a, b)) for a in range(1, h + 1, 2)
                 for b in range(2, h + 1, 2)]
        first = [e for e in edges if not (e & exceptional)]
        second = ([e for e in edges if e not in first and h not in e
                   and h - 1 not in e] if h >= 9 else [])
        residual = [e for e in edges if e not in first and e not in second]
        for seed in range(2):
            columns = []
            bulk_widths = []
            for group, g in ((first, h - 1), (second, h - 3)):
                block, _, _, _, _ = build(h, seed, group, g)
                if block:
                    block = [frozenset((1,))] * L + block + [frozenset((1,))] * L
                    columns.extend(block)
                    bulk_widths.append(len(block))
            for e in residual:
                columns.extend([frozenset((1,))] * L + [e]
                               + [frozenset((h,))] * L + [frozenset((1,))] * L)
            tested, weak = check(h, columns)
            odd_results.append({"height": h, "seed": seed, "width": len(columns),
                                "black_cells": sum(map(len, columns)),
                                "first_bulk_edges": len(first),
                                "second_bulk_edges": len(second),
                                "isolated_edges": len(residual),
                                "bulk_widths": bulk_widths,
                                "rectangles_checked": tested, "weak_presentations": weak})
    out = {"checks": results, "odd_height_checks": odd_results,
           "seconds": time.perf_counter() - start}
    Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2))
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
