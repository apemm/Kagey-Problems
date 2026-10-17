"""Enumerate all maximum blackouts of the 5 x m grid of size m+6 by SAT with blocking clauses,
using the equality structure of the row bound.

Structure (equality case of blackout <= m + floor(h^2/4) for h = 5 rows): every column is
black in exactly one row, except six columns that are black in exactly two rows, and the six
row pairs are the six edges of the complete bipartite graph K_{3,2} on a 2+3 partition of the
rows, each edge in exactly one column. There are 10 partitions (choice of the 2-set).

Encoding (per partition). One variable y[c][t] per column c and column state t, where the
11 states are the five singleton rows and the six edges. Exactly one state per column, each
edge in exactly one column. For every pair of distinct rectangles with corner symmetric
difference D, the clause "not all of D is black": a point (c, r) is white iff the state of c
does not contain r, so the clause is the disjunction over (c, r) in D of the states of c that
avoid r. A pair whose D has three points in one column, or two points in one column that are
not an edge, cannot be all black and gives no clause. Duplicate D's are merged and a D that
contains another D is dropped.

Every model is rechecked by verify_narrow.collision (equal-diagonal enumerator from the
repository root) and blocked by a clause on its column states. The enumeration stops at the
cap (default 10,000 models) or at the wall-clock limit, and says so.

Usage: python five_row_enum_structured.py WIDTH [--solver cadical153] [--cap 10000]
                                              [--minutes 30] [--out FILE]
Output JSON uses ONE-BASED (column, row) coordinates.
"""
import argparse
import json
import os
import sys
import time
from collections import defaultdict
from itertools import combinations

from pysat.solvers import Solver

import pysat

from five_row_common import (DATA_DIR, collision_report, difference_sets, one_based,
                             points_of, prune_supersets, verify_narrow)

ROWS = 5


def partitions():
    """The ten 2+3 partitions, as (two_set, three_set), two_set sorted."""
    out = []
    for q in combinations(range(ROWS), 2):
        p = tuple(r for r in range(ROWS) if r not in q)
        out.append((q, p))
    return out


def build_instance(cols, two, three, diffs):
    """Clauses of the structured encoding for one partition. Returns (clauses, states, var)."""
    edges = [tuple(sorted((a, b))) for a in two for b in three]
    states = [(r,) for r in range(ROWS)] + edges        # 11 states
    edge_set = set(edges)
    nstate = len(states)

    def var(c, t):
        return 1 + c * nstate + t

    clauses = []
    # exactly one state per column
    for c in range(cols):
        clauses.append([var(c, t) for t in range(nstate)])
        for t1, t2 in combinations(range(nstate), 2):
            clauses.append([-var(c, t1), -var(c, t2)])
    # every edge in exactly one column
    for k, e in enumerate(edges):
        t = ROWS + k
        clauses.append([var(c, t) for c in range(cols)])
        for c1, c2 in combinations(range(cols), 2):
            clauses.append([-var(c1, t), -var(c2, t)])
    # avoid[r] = states that do not contain row r; avoid_edge[e] = states other than e
    avoid = {r: [t for t, s in enumerate(states) if r not in s] for r in range(ROWS)}
    structural = len(clauses)
    skipped = 0
    seen = set()
    for d in diffs:
        bycol = defaultdict(list)
        for x, y in points_of(d, ROWS, cols):
            bycol[x].append(y)
        lits = []
        dead = False
        for c, ys in bycol.items():
            if len(ys) >= 3:
                dead = True
                break
            if len(ys) == 2:
                e = tuple(sorted(ys))
                if e not in edge_set:
                    dead = True
                    break
                t_e = states.index(e)
                lits.extend(var(c, t) for t in range(nstate) if t != t_e)
            else:
                lits.extend(var(c, t) for t in avoid[ys[0]])
        if dead:
            skipped += 1
            continue
        key = tuple(sorted(lits))
        if key in seen:
            continue
        seen.add(key)
        clauses.append(list(key))
    return clauses, states, var, structural, skipped


def model_points(model, cols, states, var):
    nstate = len(states)
    truth = set(l for l in model if l > 0)
    pts = []
    for c in range(cols):
        chosen = [t for t in range(nstate) if var(c, t) in truth]
        assert len(chosen) == 1
        pts.extend((c, r) for r in states[chosen[0]])
    return sorted(pts)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('width', type=int)
    ap.add_argument('--solver', default='cadical153')
    ap.add_argument('--cap', type=int, default=10000)
    ap.add_argument('--minutes', type=float, default=30.0)
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    cols = args.width
    deadline = time.time() + 60 * args.minutes
    t0 = time.time()

    rects = verify_narrow.rectangles(ROWS, cols)
    diffs_all = difference_sets(rects)
    diffs = prune_supersets(diffs_all)
    t_prep = time.time() - t0

    result = {
        'grid': {'rows': ROWS, 'cols': cols},
        'target_size': cols + 6,
        'method': 'SAT model enumeration with blocking clauses on the structured (row-bound '
                  'equality) encoding; one instance per 2+3 row partition',
        'encoding': 'column-state one-hot (5 singleton states + 6 edge states per column), '
                    'each K_{3,2} edge in exactly one column, one clause per pruned corner '
                    'symmetric difference restricted to column-feasible ones',
        'solver': args.solver, 'pysat_version': pysat.__version__,
        'python_version': sys.version.split()[0],
        'rectangles': len(rects), 'distinct_differences': len(diffs_all),
        'pruned_differences': len(diffs), 'preparation_seconds': round(t_prep, 2),
        'cap': args.cap, 'wall_limit_minutes': args.minutes,
        'coordinates': 'one-based (column, row), (1,1) top-left',
        'partitions': [], 'models': [], 'complete': True, 'status': 'complete',
    }
    total = 0
    for two, three in partitions():
        if time.time() > deadline:
            result['complete'] = False
            result['status'] = 'wall-clock limit reached before all partitions were enumerated'
            break
        t1 = time.time()
        clauses, states, var, structural, skipped = build_instance(cols, two, three, diffs)
        nvars = cols * len(states)
        entry = {'two_rows': [r + 1 for r in two], 'three_rows': [r + 1 for r in three],
                 'variables': nvars, 'clauses': len(clauses),
                 'structural_clauses': structural, 'rectangle_clauses': len(clauses) - structural,
                 'differences_skipped_by_column_structure': skipped,
                 'models': 0, 'complete': True}
        with Solver(name=args.solver, bootstrap_with=clauses) as s:
            while True:
                if total >= args.cap:
                    entry['complete'] = False
                    result['complete'] = False
                    result['status'] = f'more than {args.cap} models; enumeration stopped at the cap'
                    break
                if time.time() > deadline:
                    entry['complete'] = False
                    result['complete'] = False
                    result['status'] = 'wall-clock limit reached during enumeration'
                    break
                if not s.solve():
                    break
                model = s.get_model()
                pts = model_points(model, cols, states, var)
                mask = sum(1 << (y * cols + x) for x, y in pts)
                assert len(pts) == cols + 6
                check = collision_report(rects, mask, ROWS, cols)
                result['models'].append({'partition_two_rows': [r + 1 for r in two],
                                         'points': one_based(pts),
                                         'verify_narrow_valid': check is None,
                                         'collision': check})
                entry['models'] += 1
                total += 1
                # block exactly this column-state assignment
                s.add_clause([-l for l in model if l > 0 and l <= nvars])
        entry['seconds'] = round(time.time() - t1, 2)
        result['partitions'].append(entry)
        if not result['complete']:
            break
    result['model_count'] = total
    result['all_models_verified'] = all(m['verify_narrow_valid'] for m in result['models'])
    result['wall_seconds'] = round(time.time() - t0, 2)
    out = args.out or os.path.join(DATA_DIR, f'five_row_optima_structured_w{cols}_{args.solver}.json')
    with open(out, 'w') as f:
        json.dump(result, f, indent=1)
    print(f'width {cols}: {total} models, complete={result["complete"]}, '
          f'all verified={result["all_models_verified"]}, {result["wall_seconds"]} s -> {out}')


if __name__ == '__main__':
    main()
