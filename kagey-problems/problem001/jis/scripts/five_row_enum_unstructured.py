"""Enumerate all blackouts of the 5 x m grid with at least m+6 points by SAT with blocking
clauses, from the definition alone (no row-bound structure).

Encoding. One variable per grid point (black = true), indexed 1 + 5*column + row. For every
pair of distinct rectangles with corner symmetric difference D, the clause "some point of D is
white" (Lemma 1 of PROBLEM.md: two rectangles present alike iff their symmetric difference is
black). Duplicate D's are merged and supersets dropped. The cardinality constraint "at least
m+6 black points" is a totalizer from pysat.card. Rectangles are enumerated by the 4-subset
pairing test of solver/brute.py (no code shared with verify_narrow.rectangles), and the count
is compared with verify_narrow's.

Each model is rechecked by verify_narrow.collision and blocked by the clause that negates the
full point assignment, so a blackout of m+7 or more points would also be found if one existed.
The run stops at the cap or at the wall-clock limit (the solver process is stopped by the
parent, see supervised_solver.py) and says so.

Usage: python five_row_enum_unstructured.py WIDTH [--solver glucose4] [--cap 10000]
                                                [--minutes 30] [--excess 6] [--out FILE]
Output JSON uses ONE-BASED (column, row) coordinates.
"""
import argparse
import json
import os
import sys
import time

import pysat
from pysat.card import CardEnc, EncType
from supervised_solver import SupervisedSolver

from five_row_common import (DATA_DIR, collision_report, difference_sets, one_based,
                             points_of, prune_supersets, rectangles_by_quads, verify_narrow)

ROWS = 5


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('width', type=int)
    ap.add_argument('--solver', default='glucose4')
    ap.add_argument('--cap', type=int, default=10000)
    ap.add_argument('--minutes', type=float, default=30.0)
    ap.add_argument('--excess', type=int, default=6,
                    help='target size is width + excess (default 6, the row bound)')
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    cols = args.width
    target = cols + args.excess
    t0 = time.time()
    deadline = t0 + 60 * args.minutes

    rects = rectangles_by_quads(ROWS, cols)
    rects_vn = verify_narrow.rectangles(ROWS, cols)
    assert rects == rects_vn, 'the two rectangle enumerators disagree'
    diffs_all = difference_sets(rects)
    diffs = prune_supersets(diffs_all)

    def var(x, y):
        return 1 + ROWS * x + y

    npts = ROWS * cols
    clauses = []
    for d in diffs:
        clauses.append([-var(x, y) for x, y in points_of(d, ROWS, cols)])
    card = CardEnc.atleast(lits=list(range(1, npts + 1)), bound=target,
                           top_id=npts, encoding=EncType.totalizer)
    clauses.extend(card.clauses)
    nvars = max(npts, card.nv)
    t_prep = time.time() - t0

    result = {
        'grid': {'rows': ROWS, 'cols': cols}, 'target_size': target,
        'method': 'SAT model enumeration with blocking clauses on the unstructured encoding '
                  '(point variables, all pruned difference clauses, cardinality >= m+6)',
        'encoding': 'point variables 1+5*column+row; one clause per pruned corner symmetric '
                    'difference; totalizer for at least m+6 black points',
        'solver': args.solver, 'pysat_version': pysat.__version__,
        'python_version': sys.version.split()[0],
        'rectangles': len(rects), 'rectangles_match_verify_narrow': True,
        'distinct_differences': len(diffs_all), 'pruned_differences': len(diffs),
        'variables': nvars, 'clauses': len(clauses),
        'difference_clauses': len(diffs), 'cardinality_clauses': len(card.clauses),
        'preparation_seconds': round(t_prep, 2),
        'cap': args.cap, 'wall_limit_minutes': args.minutes,
        'coordinates': 'one-based (column, row), (1,1) top-left',
        'models': [], 'complete': True, 'status': 'complete',
    }

    # the solver runs in a worker process that is killed at the deadline (supervised_solver.py)
    with SupervisedSolver(args.solver, bootstrap_with=clauses) as s:
        while True:
            if len(result['models']) >= args.cap:
                result['complete'] = False
                result['status'] = f'more than {args.cap} models; enumeration stopped at the cap'
                break
            sat = s.solve_limited(timeout=max(0.0, deadline - time.time()))
            if sat is None:
                result['complete'] = False
                result['status'] = 'unresolved: wall-clock limit reached; solver process stopped'
                break
            if not sat:
                break
            model = s.get_model()
            truth = set(l for l in model if 0 < l <= npts)
            pts = sorted((x, y) for x in range(cols) for y in range(ROWS) if var(x, y) in truth)
            mask = sum(1 << (y * cols + x) for x, y in pts)
            check = collision_report(rects, mask, ROWS, cols)
            result['models'].append({'size': len(pts), 'points': one_based(pts),
                                     'verify_narrow_valid': check is None,
                                     'collision': check})
            s.add_clause([-var(x, y) if var(x, y) in truth else var(x, y)
                          for x in range(cols) for y in range(ROWS)])
    result['model_count'] = len(result['models'])
    result['sizes_found'] = sorted(set(m['size'] for m in result['models']))
    result['all_models_verified'] = all(m['verify_narrow_valid'] for m in result['models'])
    result['wall_seconds'] = round(time.time() - t0, 2)
    out = args.out or os.path.join(DATA_DIR, f'five_row_optima_unstructured_w{cols}_{args.solver}.json' if args.excess == 6 else f'five_row_size{target}_unstructured_w{cols}_{args.solver}.json')
    with open(out, 'w') as f:
        json.dump(result, f, indent=1)
    print(f'width {cols}: {result["model_count"]} models, sizes {result["sizes_found"]}, '
          f'complete={result["complete"]} ({result["status"]}), '
          f'all verified={result["all_models_verified"]}, {result["wall_seconds"]} s -> {out}')


if __name__ == '__main__':
    main()
