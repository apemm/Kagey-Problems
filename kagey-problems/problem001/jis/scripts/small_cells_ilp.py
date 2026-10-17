"""Minimum kept set on the 6 x 7, 6 x 8 and 7 x 7 grids by integer programming.

The kept set K must meet every inclusion-minimal pairwise symmetric difference of two
rectangles (Lemma 1 in PROBLEM.md); the maximum blackout is h*m minus the minimum |K|.
Two solvers on the same hitting-set formulation, each with a wall-clock limit of 30 minutes
per instance; a run that hits the limit is recorded as unresolved with its best bound.

  HiGHS through scipy.optimize.milp (rectangles from verify_narrow.rectangles).
  CBC through PuLP, as in solver/engine.py (rectangles from solver/enumerate.py, pruned
  table from solver/table.py).

Output: jis/data/small_cells_ilp.json; witnesses as one-based (column, row).
Usage: python small_cells_ilp.py [highs|cbc] [cells ...]
"""
import json
import os
import sys
import time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, ROOT)

from verify_narrow import collision, rectangles

CAP_SECONDS = 1800


def bits(x):
    return [i for i in range(x.bit_length()) if x >> i & 1]


def minimal_differences(rects):
    diffs = {a ^ b for a, b in combinations(rects, 2)}
    kept = []
    for d in sorted(diffs, key=lambda d: d.bit_count()):
        if not any(k & d == k for k in kept if k != d):
            kept.append(d)
    return kept


def run_highs(rows, cols):
    import numpy as np
    import scipy
    from scipy.optimize import Bounds, LinearConstraint, milp
    from scipy.sparse import lil_matrix
    rects = rectangles(rows, cols)
    kept = minimal_differences(rects)
    n = rows * cols
    A = lil_matrix((len(kept), n))
    for r, d in enumerate(kept):
        for i in bits(d):
            A[r, i] = 1
    t0 = time.time()
    res = milp(c=np.ones(n), constraints=LinearConstraint(A.tocsr(), lb=1, ub=np.inf),
               integrality=np.ones(n), bounds=Bounds(0, 1),
               options={'time_limit': CAP_SECONDS, 'disp': False})
    dt = time.time() - t0
    rec = {'grid': f'{rows}x{cols}', 'method': 'ILP minimum hitting set',
           'solver': f'HiGHS via scipy.optimize.milp (scipy {scipy.__version__})',
           'rectangles': len(rects), 'constraints': len(kept), 'variables': n,
           'seconds': round(dt, 1), 'scipy_status': int(res.status), 'message': res.message}
    if res.status == 0 and res.x is not None:
        kept_size = int(round(res.fun))
        black = sum(1 << i for i in range(n) if res.x[i] < 0.5)
        rec.update({'status': 'optimal', 'min_kept': kept_size, 'max_blackout': n - kept_size,
                    'witness': sorted((i % cols + 1, i // cols + 1) for i in bits(black)),
                    'witness_valid_by_verify_narrow': collision(rects, black) is None})
    else:
        rec.update({'status': 'unresolved',
                    'incumbent': None if res.x is None else int(round(res.fun)),
                    'lower_bound_on_kept': getattr(res, 'mip_dual_bound', None)})
    return rec


def run_cbc(rows, cols):
    import pulp
    from solver.enumerate import grid_points, rectangles as rects_engine
    from solver.table import difference_table, prune
    pts = grid_points(rows, cols)
    idx = {p: k for k, p in enumerate(pts)}
    n = len(pts)
    rects = rects_engine(rows, cols)
    pruned = prune(difference_table(rects))
    prob = pulp.LpProblem('min_hitting_set', pulp.LpMinimize)
    x = [pulp.LpVariable(f'x{k}', cat='Binary') for k in range(n)]
    prob += pulp.lpSum(x)
    for row in pruned:
        prob += pulp.lpSum(x[idx[p]] for p in row) >= 1
    t0 = time.time()
    status = prob.solve(pulp.PULP_CBC_CMD(msg=False, timeLimit=CAP_SECONDS))
    dt = time.time() - t0
    rec = {'grid': f'{rows}x{cols}', 'method': 'ILP minimum hitting set',
           'solver': f'CBC via PuLP {pulp.__version__} (solver/engine.py formulation)',
           'rectangles': len(rects), 'constraints': len(pruned), 'variables': n,
           'seconds': round(dt, 1), 'pulp_status': pulp.LpStatus[status]}
    if pulp.LpStatus[status] == 'Optimal' and dt < CAP_SECONDS - 5:
        kept_size = int(round(pulp.value(prob.objective)))
        black_pts = [p for k, p in enumerate(pts) if pulp.value(x[k]) < 0.5]
        # engine points are one-based (column, row) already
        vn = rectangles(rows, cols)
        black = sum(1 << ((j - 1) * cols + (i - 1)) for i, j in black_pts)
        rec.update({'status': 'optimal', 'min_kept': kept_size, 'max_blackout': n - kept_size,
                    'witness': sorted(black_pts),
                    'witness_valid_by_verify_narrow': collision(vn, black) is None})
    else:
        rec.update({'status': 'unresolved',
                    'note': 'time limit reached; CBC reports its incumbent as Optimal only when proved'})
    return rec


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else 'highs'
    cells = sys.argv[2:] or ['6x7', '6x8', '7x7']
    out = []
    for cell in cells:
        rows, cols = map(int, cell.split('x'))
        rec = run_highs(rows, cols) if which == 'highs' else run_cbc(rows, cols)
        print(json.dumps(rec), flush=True)
        out.append(rec)
        with open(os.path.join(ROOT, 'jis', 'data', f'small_cells_ilp_{which}.json'), 'w') as fh:
            json.dump(out, fh, indent=1)


if __name__ == '__main__':
    main()
