"""Solver-free count of the valid blackouts of m+6 points on the 5 x m grid.

A valid blackout of m+6 points on five rows has every column black in exactly
one row or in the two rows of one edge of a complete bipartite graph K_{2,3}
on the rows, each of the six edges in exactly one column (row-bound equality:
the row-column incidence graph has no 4- or 6-cycle, the tree-reduced row
graph is triangle-free with m+6-m = 6 edges, so it is K_{2,3}, and a column
with three black rows would close a 6-cycle through the other side).  For each
of the ten 2+3 row partitions this script walks the columns from left to
right, each column a singleton or an unused edge, and prunes a prefix as soon
as two rectangles lying inside it have the same visible corners (a restriction
of a valid blackout to an interval of columns is valid).  Every complete board
is a valid blackout of m+6 points; the count is a_5(m).

No SAT solver is involved.  Rectangles and the presentation test come from
five_row_geometry_check (corner plus two perpendicular side vectors).  Each
width runs under a wall-clock cap; a width that does not finish is recorded
as unresolved with the partitions completed so far.

Output: jis/data/five_row_count_dfs_check.json; models in one-based
(column, row) coordinates for widths up to 9, counts only beyond.

Usage: five_row_count_dfs_check.py [--out FILE] [--partition a,b] [width ...]   (default 6..12)
(--partition a,b restricts the run to the 2+3 partition whose two-row side is rows a, b, one-based)
"""
import json
import os
import sys
import time
from itertools import combinations

from five_row_geometry_check import (rectangles_by_max_column, rectangles_by_sides,
                                     presentation_collision, one_based_from_mask)

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, '..', 'data')
ROWS = 5
CAP_SECONDS = 1200


class Timeout(Exception):
    pass


def count_partition(cols, two, groups, deadline, keep_models):
    three = [r for r in range(ROWS) if r not in two]
    edges = [(a, b) for a in two for b in three]
    singles = [(1 << (r * cols), None) for r in range(ROWS)]
    doubles = [((1 << (a * cols)) | (1 << (b * cols)), i) for i, (a, b) in enumerate(edges)]
    seen = {}
    models = []
    stats = {'nodes': 0, 'count': 0}

    def place(c, black, used, ndoubles):
        stats['nodes'] += 1
        if stats['nodes'] % 100000 == 0 and time.time() > deadline:
            raise Timeout
        if c == cols:
            if ndoubles == 6:
                stats['count'] += 1
                if keep_models:
                    models.append(black)
            return
        remaining = cols - c
        if 6 - ndoubles > remaining:
            return
        options = singles if ndoubles == 6 else singles + doubles
        if 6 - ndoubles == remaining:
            options = doubles
        for colmask, edge in options:
            if edge is not None and used >> edge & 1:
                continue
            nb = black | (colmask << c)
            added = []
            ok = True
            for r in groups[c]:
                shown = r & ~nb
                if shown in seen:
                    ok = False
                    break
                seen[shown] = 1
                added.append(shown)
            if ok:
                place(c + 1, nb, used | (0 if edge is None else 1 << edge),
                      ndoubles + (0 if edge is None else 1))
            for shown in added:
                del seen[shown]

    place(0, 0, 0, 0)
    return stats['count'], stats['nodes'], models


def run_width(cols, only=None):
    t0 = time.time()
    deadline = t0 + CAP_SECONDS
    groups = rectangles_by_max_column(ROWS, cols)
    rects = rectangles_by_sides(ROWS, cols)
    keep = cols <= 9
    rec = {'width': cols, 'target_points': cols + 6, 'rectangles': len(rects), 'partitions': [],
           'status': 'complete'}
    if only is not None:
        rec['only_partition_two_rows_one_based'] = [r + 1 for r in only]
    total = 0
    all_models = []
    for two in combinations(range(ROWS), 2):
        if only is not None and two != only:
            continue
        t1 = time.time()
        try:
            count, nodes, models = count_partition(cols, two, groups, deadline, keep)
        except Timeout:
            rec['status'] = 'unresolved'
            rec['partitions'].append({'two_rows_one_based': [r + 1 for r in two], 'status': 'unresolved',
                                      'seconds': round(time.time() - t1, 1)})
            break
        rec['partitions'].append({'two_rows_one_based': [r + 1 for r in two], 'count': count,
                                  'nodes': nodes, 'seconds': round(time.time() - t1, 1)})
        total += count
        if keep:
            for b in models:
                assert b.bit_count() == cols + 6
                assert presentation_collision(rects, b) is None
                all_models.append(b)
    if rec['status'] == 'complete':
        rec['count'] = total
        if keep:
            assert len(set(all_models)) == total
            rec['models_one_based'] = [one_based_from_mask(b, ROWS, cols) for b in all_models]
            rec['models_recheck'] = 'every model passed the full presentation test and all are distinct'
            if cols == 8:
                pts = [set(map(tuple, m)) for m in rec['models_one_based']]
                sym = lambda s, f: {f(c, r) for c, r in s}
                images = lambda s: [s, sym(s, lambda c, r: (c, 6 - r)), sym(s, lambda c, r: (9 - c, r)),
                                    sym(s, lambda c, r: (9 - c, 6 - r))]
                rec['width8_one_klein_orbit'] = all(any(im == q for q in pts) for s in pts for im in images(s)) \
                    and len(pts) == 4 and len({frozenset(im) for im in images(pts[0])}) == 4
    rec['seconds'] = round(time.time() - t0, 1)
    return rec


def main():
    args = sys.argv[1:]
    name = 'five_row_count_dfs_check.json'
    if '--out' in args:
        i = args.index('--out')
        name = args[i + 1]
        del args[i:i + 2]
    only = None
    if '--partition' in args:
        i = args.index('--partition')
        only = tuple(sorted(int(r) - 1 for r in args[i + 1].split(',')))
        del args[i:i + 2]
    widths = [int(a) for a in args] or list(range(6, 13))
    path = os.path.join(DATA, name)
    out = {'method': 'column-by-column search over the row-bound equality structure with prefix pruning',
           'solver': 'none', 'python_version': sys.version.split()[0], 'cap_seconds': CAP_SECONDS,
           'coordinates': 'one-based (column,row)', 'widths': {}}
    if os.path.exists(path):
        with open(path) as f:
            out = json.load(f)
    for m in widths:
        rec = run_width(m, only)
        out['widths'][str(m)] = rec
        print(json.dumps({k: v for k, v in rec.items() if k != 'models_one_based'}), flush=True)
        with open(path, 'w') as f:
            json.dump(out, f, indent=1)


if __name__ == '__main__':
    main()
