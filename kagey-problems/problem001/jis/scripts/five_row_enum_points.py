"""Enumerate the blackouts of m+6 points of the 5 x m grid by SAT with blocking clauses,
point-variable encoding with the equality structure of the row bound.

Hypothesis (equality theorem, research notes): every column is black in exactly one row except
six columns black in exactly the two rows of one edge of the complete bipartite graph K_{2,3}
on a 2+3 partition of the rows, each edge in exactly one column. One instance per partition
(10 partitions).

Variables: one per grid point (black = true, index 1 + 5*column + row) and one indicator per
(edge, column). Clauses: every column has at least one black point and at most two; two black
points in a column must be an edge of the partition, and then the indicator of that edge and
column is true; an indicator forces both points black; each edge has exactly one column. For
every pair of distinct rectangles with corner symmetric difference D (verify_narrow.rectangles),
the clause "some point of D is white" on the point variables, dropping D's that contain a
smaller D and D's with three points in one column or two points in one column that are not
an edge of the partition.

Restrictions: --singleton-rows (one-based rows allowed for singleton columns) and
--double-columns (one-based columns that must carry the six doubles).

Each model is rechecked with verify_narrow.collision and blocked by negating its point
assignment. The run stops at the cap (counted over all partitions) or at the wall-clock limit.

Usage: python five_row_enum_points.py WIDTH [--solver cadical153] [--cap 10000] [--minutes 30]
          [--singleton-rows 1] [--double-columns 1,5,9,13,17,21] [--out FILE] [--tag NAME]
Output JSON: ONE-BASED (column, row) points, (1,1) top-left.
"""
import argparse
import json
import os
import sys
import time
from itertools import combinations

import pysat
from pysat.solvers import Solver

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, ROOT)
import verify_narrow  # noqa: E402

DATA_DIR = os.path.join(HERE, '..', 'data')
ROWS = 5


def minimal_differences(rects):
    diffs = {a ^ b for a, b in combinations(rects, 2)}
    kept, keptset = [], set()
    for d in sorted(diffs, key=lambda d: bin(d).count('1')):
        bits = [1 << i for i in range(d.bit_length()) if d >> i & 1]
        redundant = False
        for n in range(1, len(bits)):
            for sub in combinations(bits, n):
                if sum(sub) in keptset:
                    redundant = True
                    break
            if redundant:
                break
        if not redundant:
            kept.append(d)
            keptset.add(d)
    return len(diffs), kept


def instance(cols, two, three, diffs, srows, dcols):
    edges = sorted(tuple(sorted((a, b))) for a in two for b in three)
    edge_set = set(edges)

    def p(c, r):
        return 1 + c * ROWS + r
    npts = cols * ROWS

    def z(e, c):
        return 1 + npts + e * cols + c
    clauses = []
    for c in range(cols):
        clauses.append([p(c, r) for r in range(ROWS)])
        for a, b, d in combinations(range(ROWS), 3):
            clauses.append([-p(c, a), -p(c, b), -p(c, d)])
        for a, b in combinations(range(ROWS), 2):
            if (a, b) in edge_set:
                e = edges.index((a, b))
                clauses.append([-p(c, a), -p(c, b), z(e, c)])
                clauses.append([-z(e, c), p(c, a)])
                clauses.append([-z(e, c), p(c, b)])
            else:
                clauses.append([-p(c, a), -p(c, b)])
    for e in range(len(edges)):
        clauses.append([z(e, c) for c in range(cols)])
        for c1, c2 in combinations(range(cols), 2):
            clauses.append([-z(e, c1), -z(e, c2)])
    structural = len(clauses)
    if srows is not None:
        for c in range(cols):
            for r in range(ROWS):
                if r in srows:
                    continue
                # a black point in a forbidden singleton row must be part of a double
                clauses.append([-p(c, r)] + [p(c, s) for s in range(ROWS) if s != r])
    if dcols is not None:
        for c in range(cols):
            if c in dcols:
                clauses.append([z(e, c) for e in range(len(edges))])
            else:
                for e in range(len(edges)):
                    clauses.append([-z(e, c)])
    restriction = len(clauses) - structural
    skipped = 0
    for d in diffs:
        bycol = {}
        for i in range(d.bit_length()):
            if d >> i & 1:
                bycol.setdefault(i % cols, []).append(i // cols)
        dead = any(len(ys) >= 3 or (len(ys) == 2 and tuple(sorted(ys)) not in edge_set)
                   for ys in bycol.values())
        if dead:
            skipped += 1
            continue
        clauses.append([-p(c, y) for c, ys in bycol.items() for y in ys])
    return clauses, edges, p, npts, structural, restriction, skipped, npts + len(edges) * cols


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('width', type=int)
    ap.add_argument('--solver', default='cadical153')
    ap.add_argument('--cap', type=int, default=10000)
    ap.add_argument('--minutes', type=float, default=30.0)
    ap.add_argument('--singleton-rows', default=None)
    ap.add_argument('--double-columns', default=None)
    ap.add_argument('--out', default=None)
    ap.add_argument('--tag', default='')
    args = ap.parse_args()
    cols = args.width
    t0 = time.time()
    deadline = t0 + 60 * args.minutes
    srows = None if not args.singleton_rows else {int(r) - 1 for r in args.singleton_rows.split(',')}
    dcols = None if not args.double_columns else {int(x) - 1 for x in args.double_columns.split(',')}

    rects = verify_narrow.rectangles(ROWS, cols)
    n_all, diffs = minimal_differences(rects)
    t_prep = time.time() - t0
    result = {
        'grid': {'rows': ROWS, 'cols': cols}, 'target_size': cols + 6,
        'method': 'SAT model enumeration with blocking clauses, point-variable encoding with '
                  'the equality structure (K_{2,3} row pairs, each edge once), one instance '
                  'per 2+3 row partition',
        'solver': args.solver, 'pysat_version': pysat.__version__,
        'python_version': sys.version.split()[0],
        'rectangles': len(rects), 'rectangle_enumerator': 'verify_narrow.rectangles (equal diagonals)',
        'distinct_differences': n_all, 'minimal_differences': len(diffs),
        'preparation_seconds': round(t_prep, 2),
        'cap': args.cap, 'wall_limit_minutes': args.minutes,
        'singleton_rows_allowed': sorted(r + 1 for r in srows) if srows else list(range(1, ROWS + 1)),
        'double_columns': sorted(c + 1 for c in dcols) if dcols else None,
        'coordinates': 'one-based (column, row), (1,1) top-left',
        'partitions': [], 'models': [], 'complete': True, 'status': 'complete',
    }
    total = 0
    stop = False
    for two in combinations(range(ROWS), 2):
        three = tuple(r for r in range(ROWS) if r not in two)
        t1 = time.time()
        clauses, edges, p, npts, structural, restriction, skipped, nvars = \
            instance(cols, two, three, diffs, srows, dcols)
        entry = {'two_rows': [r + 1 for r in two], 'three_rows': [r + 1 for r in three],
                 'variables': nvars, 'clauses': len(clauses), 'structural_clauses': structural,
                 'restriction_clauses': restriction,
                 'rectangle_clauses': len(clauses) - structural - restriction,
                 'differences_skipped_by_column_structure': skipped,
                 'models': 0, 'complete': True}
        with Solver(name=args.solver, bootstrap_with=clauses) as s:
            while True:
                if total >= args.cap:
                    entry['complete'] = False
                    result['status'] = f'more than {args.cap} models; enumeration stopped at the cap'
                    stop = True
                    break
                if time.time() > deadline:
                    entry['complete'] = False
                    result['status'] = 'wall-clock limit reached during enumeration'
                    stop = True
                    break
                if not s.solve():
                    break
                model = s.get_model()
                truth = set(l for l in model if 0 < l <= npts)
                pts = sorted((c, r) for c in range(cols) for r in range(ROWS) if p(c, r) in truth)
                assert len(pts) == cols + 6
                mask = sum(1 << (y * cols + x) for x, y in pts)
                pair = verify_narrow.collision(rects, mask)
                result['models'].append({'partition_two_rows': [r + 1 for r in two],
                                         'points': [[x + 1, y + 1] for x, y in pts],
                                         'verify_narrow_valid': pair is None})
                entry['models'] += 1
                total += 1
                s.add_clause([-p(c, r) if p(c, r) in truth else p(c, r)
                              for c in range(cols) for r in range(ROWS)])
        entry['seconds'] = round(time.time() - t1, 2)
        result['partitions'].append(entry)
        if stop:
            result['complete'] = False
            break
    result['model_count'] = total
    result['all_models_verified'] = all(m['verify_narrow_valid'] for m in result['models'])
    result['wall_seconds'] = round(time.time() - t0, 2)
    tag = args.tag or (f'w{cols}' + (f'_srows{args.singleton_rows.replace(",", "")}' if args.singleton_rows else '')
                       + (f'_dcols{args.double_columns.replace(",", "-")}' if args.double_columns else ''))
    out = args.out or os.path.join(DATA_DIR, f'five_row_enum_points_{tag}_{args.solver}.json')
    with open(out, 'w') as f:
        json.dump(result, f, indent=1)
    print(f'width {cols}: {total} models, complete={result["complete"]} ({result["status"]}), '
          f'all verified={result["all_models_verified"]}, {result["wall_seconds"]} s -> {out}')


if __name__ == '__main__':
    main()
