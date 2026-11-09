"""Bounded positional resampling examples, followed by exact board checks.

The proof uses a sufficiently large absolute constant. These runs use a smaller
empirical interval and report successes only; they do not certify that constant.
"""

from itertools import combinations
from math import isqrt
from pathlib import Path
import json
import random
import time

from threshold_progress_check import tilts, mixed_supports, grouped, check


def prepare(h, edges, g):
    three = {tuple(sorted(T)) for R in tilts(h) for T in combinations(R, 3)}
    four = set(mixed_supports(h))
    supports = [grouped(S) for S in sorted(three | four)]
    influences = []
    for e in edges:
        offsets = set()
        for cols in supports:
            for center, rows in cols.items():
                if rows <= e and all(len(rs) == 1 and rs <= {1, g}
                                     for x, rs in cols.items() if x != center):
                    offsets.update(x - center for x in cols if x != center)
        influences.append(offsets | {0})
    return supports, influences


def find_event(h, edges, g, positions, supports, influences):
    claims = {}
    for i, (x, offsets) in enumerate(zip(positions, influences)):
        for d in offsets:
            if x + d in claims:
                return (i, claims[x + d]), "overlap"
            claims[x + d] = i
    owners = dict(zip(positions, range(len(edges))))
    row_positions = {}
    for i, e in enumerate(edges):
        for row in e:
            row_positions.setdefault(row, []).append(positions[i])
    for support in supports:
        shifts = {x - offset for offset, rows in support.items()
                  for row in rows for x in row_positions.get(row, [])}
        for shift in shifts:
            labels = set()
            possible = True
            for offset, rows in support.items():
                index = owners.get(shift + offset)
                if index is not None and rows & edges[index]:
                    if not rows <= edges[index]:
                        possible = False
                        break
                    labels.add(index)
                elif len(rows) != 1 or not rows <= {1, g}:
                    possible = False
                    break
            if possible and len(labels) >= 2:
                return tuple(sorted(labels)), "support"
    for i, j in combinations(range(len(edges)), 2):
        dx = positions[j] - positions[i]
        if dx % 2:
            continue  # A vertical alternative has the same midpoint column.
        for r in edges[i]:
            for s in edges[j]:
                n = dx * dx + (r - s) ** 2
                length = isqrt(n)
                if length * length != n or length % 2 == 0:
                    continue
                if (r + s - length) % 2:
                    continue
                lo, hi = (r + s - length) // 2, (r + s + length) // 2
                if 1 <= lo < hi <= h:
                    return (i, j), "vertical"
    return None


def sample_block(h, edges, g, seed):
    if not edges:
        return [], {"edges": 0}
    supports, influences = prepare(h, edges, g)
    rng = random.Random(seed)
    interval = 128 * len(edges)
    positions = [rng.randrange(interval) for _ in edges]
    counts = {"overlap": 0, "support": 0, "vertical": 0}
    started = time.perf_counter()
    for iteration in range(2000):
        failure = find_event(h, edges, g, positions, supports, influences)
        if failure is None:
            break
        if time.perf_counter() - started > 45:
            raise RuntimeError((h, "bounded resampling timeout", counts))
        labels, kind = failure
        counts[kind] += 1
        for i in labels:
            positions[i] = rng.randrange(interval)
    else:
        raise RuntimeError((h, "resampling iteration cap", counts))
    W = 1 + (h - 1) ** 2 // 4
    low, high = min(positions) - 2 * W, max(positions) + 2 * W
    word = [frozenset((rng.choice((1, g)),)) for _ in range(high - low + 1)]
    for e, x, offsets in zip(edges, positions, influences):
        for d in offsets:
            word[x + d - low] = e if not d else frozenset((1 if d < 0 else g,))
    L = 2 * W
    word = [frozenset((1,))] * L + word + [frozenset((1,))] * L
    return word, {"edges": len(edges), "sea_top": g, "interval": interval,
                  "positions": positions, "resampling": counts,
                  "max_influence_size": max(map(len, influences)),
                  "width_with_collars": len(word)}


def good(h, edge, g):
    if max(edge) > g:
        return False
    r = next(r for r in edge if r % 2)
    return all(r - j < 1 or isqrt(j * (g - r + j)) ** 2 != j * (g - r + j)
               for j in range(1, h - g + 1))


def complete(h, seed):
    edges = [frozenset((a, b)) for a in range(1, h + 1, 2)
             for b in range(2, h + 1, 2)]
    backgrounds = [(h, False)] if h % 2 == 0 else [
        (h - 1, False), (h - 1, True), (h - 3, False), (h - 3, True)]
    groups = [[] for _ in backgrounds]
    for e in edges:
        for i, (g, reflect) in enumerate(backgrounds):
            f = frozenset(h + 1 - r for r in e) if reflect else e
            if good(h, f, g):
                groups[i].append(f)
                break
        else:
            raise AssertionError((h, "background cover", e))
    word, details = [], []
    L = 2 * (1 + (h - 1) ** 2 // 4)
    last_anchor = None
    for i, ((g, reflect), group) in enumerate(zip(backgrounds, groups)):
        if not group:
            continue
        block, info = sample_block(h, group, g, seed + 37 * i)
        if reflect:
            block = [frozenset(h + 1 - r for r in c) for c in block]
        anchor = h if reflect else 1
        if last_anchor is not None and last_anchor != anchor:
            word.extend([frozenset((last_anchor,))] * L + [frozenset((anchor,))] * L)
        word.extend(block)
        last_anchor = anchor
        info["reflected"] = reflect
        details.append(info)
    tested, weak = check(h, word)
    return {"height": h, "seed": seed, "width": len(word),
            "black_cells": sum(map(len, word)), "blocks": details,
            "rectangles_checked": tested, "weak_presentations": weak}


def main():
    started = time.perf_counter()
    results = [complete(h, 41 + h) for h in (4, 6, 8, 9)]
    out = {"checks": results, "seconds": time.perf_counter() - started}
    Path(__file__).with_suffix(".json").write_text(json.dumps(out, indent=2))
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
