"""Exhaustive structured search for six-row blackouts of m+9 points.

A blackout of m+9 points on 6 rows and m columns has every column black in one
or two rows, exactly nine double columns, and the nine row pairs of the doubles
are the nine edges of a K_{3,3} on the rows, each once (incidence graph without
C4 or C6, spanning trees per column, Mantel).  This script enumerates every such
blackout for one partition of the rows into two triples by depth-first search
over the columns from left to right, pruning as soon as two rectangles lying in
the placed columns show the same visible corners (a collision in a prefix cannot
be repaired by later columns).  It is an enumeration, not a SAT call, and it
shares no code with the structured SAT encoders.

Usage: python six_row_dfs_check.py WIDTH PARTITION_INDEX CAP_SECONDS OUT.json
PARTITION_INDEX 0..9 picks the triple containing row 1 (see partitions()).
Output coordinates are one-based (column, row), (1,1) top left.
"""
import json
import os
import sys
import time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cells_common_check import rectangles_by_triples, first_collision  # noqa: E402

ROWS = 6


def partitions():
    out = []
    for other in combinations(range(2, 7), 2):
        a = (1,) + other
        b = tuple(r for r in range(1, 7) if r not in a)
        out.append((a, b))
    return out


def search(width, partition, cap, forced=None, max_store=50):
    """forced: optional dict column -> 'single'/'double' restricting column types
    (used by the periodic ansatz check); singleton row restricted to 1 when the
    column is forced single."""
    a, b = partition
    edges = [(x, y) if x < y else (y, x) for x in a for y in b]
    rects = rectangles_by_triples(ROWS, width)
    by_max = {c: [] for c in range(1, width + 1)}
    for rect in rects:
        m = sum(1 << ((c - 1) * ROWS + (r - 1)) for c, r in rect)
        by_max[max(c for c, _ in rect)].append(m)
    bit = lambda c, r: 1 << ((c - 1) * ROWS + (r - 1))
    seen = {}
    t0 = time.time()
    stats = {'nodes': 0, 'pruned': 0, 'witnesses': 0, 'stored': [], 'finished': False}
    sys.setrecursionlimit(10000)

    def place(c, black, used, doubles, rest):
        stats['nodes'] += 1
        if stats['nodes'] % 5000 == 0 and time.time() - t0 > cap:
            raise TimeoutError
        added = []
        for m in by_max[c]:
            vis = m & ~black
            if vis in seen:
                for k in added:
                    del seen[k]
                stats['pruned'] += 1
                return
            seen[vis] = m
            added.append(vis)
        if c == width:
            stats['witnesses'] += 1
            if len(stats['stored']) < max_store:
                stats['stored'].append([(cc, r) for cc in range(1, width + 1) for r in range(1, ROWS + 1)
                                        if black & bit(cc, r)])
        else:
            extend(c + 1, black, used, doubles, rest)
        for k in added:
            del seen[k]

    def extend(c, black, used, doubles, rest):
        remaining = width - c + 1
        if remaining < 9 - doubles:
            return
        kind = forced.get(c) if forced else None
        if kind != 'single' and doubles < 9:
            for i, (x, y) in enumerate(edges):
                if used >> i & 1:
                    continue
                place(c, black | bit(c, x) | bit(c, y), used | 1 << i, doubles + 1, rest)
        if kind != 'double' and remaining - 1 >= 9 - doubles:
            rows = (1,) if kind == 'single' else range(1, ROWS + 1)
            for r in rows:
                place(c, black | bit(c, r), used, doubles, rest)

    try:
        extend(1, 0, 0, 0, None)
        stats['finished'] = True
    except TimeoutError:
        stats['finished'] = False
    stats['seconds'] = round(time.time() - t0, 1)
    stats['rectangles'] = len(rects)
    for w in stats['stored']:
        assert len(w) == width + 9 and first_collision(rects, set(w)) is None
    return stats


def main():
    width, idx, cap = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    out = sys.argv[4]
    part = partitions()[idx]
    stats = search(width, part, cap)
    result = {'rows': ROWS, 'width': width, 'target': width + 9, 'partition_one_based_rows': [list(part[0]), list(part[1])],
              'method': 'exhaustive column DFS with prefix presentation pruning',
              'status': ('finished' if stats['finished'] else 'unresolved'),
              'witnesses_total': stats['witnesses'], 'witnesses_stored': stats['stored'],
              'nodes': stats['nodes'], 'pruned': stats['pruned'], 'rectangles': stats['rectangles'],
              'seconds': stats['seconds'], 'cap_seconds': cap,
              'coordinates': 'one-based (column,row), (1,1) top-left'}
    json.dump(result, open(out, 'w'), indent=1)
    print(json.dumps({k: v for k, v in result.items() if k != 'witnesses_stored'}))


if __name__ == '__main__':
    main()
