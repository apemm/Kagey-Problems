"""SAT enumeration of the maximum blackouts of the 5 x m grid with blocking clauses, in an
encoding that assumes nothing about the structure of an optimum.

Variables: one per grid point (black), one hidden indicator per rectangle. Clauses:
  - exactly m + 6 black points (totalizer encoding from pysat);
  - the indicator of a rectangle is equivalent to all four corners being black, and at most
    one indicator is true (sequential counter): two fully hidden rectangles present alike;
  - for every pair of distinct rectangles sharing a corner, not all points of their symmetric
    difference are black (two rectangles present alike iff their symmetric difference is
    black; two rectangles sharing no corner present alike only when both are hidden).
Rectangles come from the right-angle-triple enumerator. Every model is rechecked by the
injectivity of the visible-corner map and by verify_narrow.collision, and blocked by the
clause forbidding its exact black set. Optional restrictions: the columns of the doubles
(exactly two black points there and one elsewhere), the rows allowed for the singletons, and
the bound "every column black in one or two rows" (the first conclusion of the equality
theorem, without the bipartite shape of the doubles).

The run stops at the model cap or at the wall-clock cap (the solver process is stopped), and the
JSON records whether the enumeration was complete. Coordinates in the output are one-based
(column, row).

Usage: python verify21_sat_check.py WIDTH [--solver minisat22] [--cap 10001] [--minutes 20]
       [--double-columns 1,5,9,13,17,21] [--singleton-rows 1] [--column-bounds] [--tag NAME]
"""
import argparse
import json
import os
import sys
import time
from itertools import combinations

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from supervised_solver import SupervisedSolver

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.abspath(os.path.join(HERE, '..', '..')))
import verify21_common_check as C  # noqa: E402
import verify_narrow  # noqa: E402

DATA = os.path.join(HERE, '..', 'data')
ROWS = 5


def build(m, double_columns, singleton_rows, column_bounds=False):
    pool = IDPool()
    var = {(x, y): pool.id(('p', x, y)) for y in range(ROWS) for x in range(m)}
    rects = C.rectangles(ROWS, m)
    clauses = []
    # cardinality
    target = m + 6
    clauses += CardEnc.equals(lits=list(var.values()), bound=target, vpool=pool,
                              encoding=EncType.totalizer).clauses
    # hidden indicators
    hid = []
    for i, r in enumerate(rects):
        hv = pool.id(('h', i))
        hid.append(hv)
        lits = [var[p] for p in r]
        for v in lits:
            clauses.append([-hv, v])
        clauses.append([hv] + [-v for v in lits])
    clauses += CardEnc.atmost(lits=hid, bound=1, vpool=pool, encoding=EncType.seqcounter).clauses
    # differences of rectangles sharing a corner
    by_point = {}
    for i, r in enumerate(rects):
        for p in r:
            by_point.setdefault(p, []).append(i)
    diffs = set()
    for lst in by_point.values():
        for i, j in combinations(lst, 2):
            diffs.add(frozenset(rects[i] ^ rects[j]))
    for d in diffs:
        clauses.append([-var[p] for p in d])
    # restrictions
    if double_columns is not None:
        for x in range(m):
            col = [var[x, y] for y in range(ROWS)]
            k = 2 if x in double_columns else 1
            # exactly k of the five: no k+1 all black, no 5-k+1 all white
            for sub in combinations(col, k + 1):
                clauses.append([-v for v in sub])
            for sub in combinations(col, ROWS - k + 1):
                clauses.append(list(sub))
            if k == 1 and singleton_rows is not None:
                for y in range(ROWS):
                    if y not in singleton_rows:
                        clauses.append([-var[x, y]])
    elif column_bounds:
        # every column black in one or two rows (the equality theorem's first conclusion only)
        for x in range(m):
            col = [var[x, y] for y in range(ROWS)]
            clauses.append(col)
            for sub in combinations(col, 3):
                clauses.append([-v for v in sub])
        if singleton_rows is not None:
            for x in range(m):
                for y in range(ROWS):
                    if y not in singleton_rows:
                        clauses.append([-var[x, y]] + [var[x, z] for z in range(ROWS) if z != y])
    elif singleton_rows is not None:
        # a column with a point outside the allowed rows must have two black points
        for x in range(m):
            for y in range(ROWS):
                if y not in singleton_rows:
                    clauses.append([-var[x, y]] + [var[x, z] for z in range(ROWS) if z != y])
    return pool, var, rects, clauses, len(diffs)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('width', type=int)
    ap.add_argument('--solver', default='minisat22')
    ap.add_argument('--cap', type=int, default=10001)
    ap.add_argument('--minutes', type=float, default=20.0)
    ap.add_argument('--double-columns', default=None)
    ap.add_argument('--singleton-rows', default=None)
    ap.add_argument('--column-bounds', action='store_true',
                    help='every column black in one or two rows')
    ap.add_argument('--tag', default=None)
    a = ap.parse_args()
    m = a.width
    dcols = None if a.double_columns is None else {int(t) - 1 for t in a.double_columns.split(',')}
    srows = None if a.singleton_rows is None else {int(t) - 1 for t in a.singleton_rows.split(',')}
    t0 = time.time()
    deadline = t0 + 60 * a.minutes
    pool, var, rects, clauses, ndiff = build(m, dcols, srows, a.column_bounds)
    narrow_rects = verify_narrow.rectangles(ROWS, m)
    prep = time.time() - t0
    import pysat
    out = {'grid': {'rows': ROWS, 'cols': m}, 'target_size': m + 6,
           'method': 'SAT model enumeration with blocking clauses; point variables, totalizer '
                     'cardinality, hidden-rectangle indicators with at-most-one, symmetric '
                     'differences of corner-sharing rectangle pairs (no structure assumed)',
           'solver': a.solver, 'pysat_version': pysat.__version__,
           'python_version': sys.version.split()[0], 'rectangles': len(rects),
           'corner_sharing_differences': ndiff, 'variables': pool.top, 'clauses': len(clauses),
           'double_columns': None if dcols is None else sorted(c + 1 for c in dcols),
           'singleton_rows_allowed': None if srows is None else sorted(r + 1 for r in srows),
           'column_bounds_one_or_two': bool(a.column_bounds),
           'cap': a.cap, 'wall_limit_minutes': a.minutes,
           'coordinates': 'one-based (column, row), (1,1) top-left',
           'preparation_seconds': round(prep, 2), 'models': []}
    points = list(var)
    models = []
    status = 'complete'
    # the solver runs in a worker process that is killed at the deadline (supervised_solver.py)
    with SupervisedSolver(a.solver, bootstrap_with=clauses) as s:
        while len(models) < a.cap:
            remaining = deadline - time.time()
            if remaining <= 0:
                status = 'unresolved: wall-clock limit'
                break
            res = s.solve_limited(timeout=remaining)
            if res is None:
                status = 'unresolved: wall-clock limit (solver process stopped)'
                break
            if not res:
                break
            model = set(s.get_model())
            black = {p for p in points if var[p] in model}
            assert len(black) == m + 6
            ok1 = C.is_valid(rects, black)
            ok2 = verify_narrow.collision(narrow_rects, verify_narrow.mask(black, m)) is None
            shape = C.equality_shape(black, ROWS, m)
            models.append({'points': C.one_based(black), 'valid_injective': ok1,
                           'valid_verify_narrow': ok2,
                           'two_rows': None if shape is None else [r + 1 for r in shape[0]]})
            s.add_clause([-var[p] for p in black])
        else:
            status = f'more than {a.cap - 1} models; stopped at the cap'
    out['models'] = models
    out['model_count'] = len(models)
    out['complete'] = status == 'complete'
    out['status'] = status
    out['all_models_valid_injective'] = all(x['valid_injective'] for x in models)
    out['all_models_valid_verify_narrow'] = all(x['valid_verify_narrow'] for x in models)
    out['all_models_have_equality_structure'] = all(x['two_rows'] is not None for x in models)
    per = {}
    for x in models:
        key = 'none' if x['two_rows'] is None else ','.join(map(str, x['two_rows']))
        per[key] = per.get(key, 0) + 1
    out['models_per_two_row_side'] = per
    out['wall_seconds'] = round(time.time() - t0, 2)
    tag = a.tag or (f'w{m}_{a.solver}' + ('' if dcols is None else '_dcols') +
                    ('' if srows is None else '_srows' + a.singleton_rows.replace(',', '')))
    with open(os.path.join(DATA, f'verify21_sat_{tag}.json'), 'w') as f:
        json.dump(out, f, indent=1)
    print({k: v for k, v in out.items() if k != 'models'})


if __name__ == '__main__':
    main()
