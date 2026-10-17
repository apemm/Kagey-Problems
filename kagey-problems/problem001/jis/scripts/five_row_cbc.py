r"""Five rows, ILP (CBC through PuLP) value of the maximum blackout with a time limit.

Same pipeline as solver/engine.py (solver.enumerate.rectangles, solver.table
difference table and pruning, minimum hitting set by CBC), but with a wall-clock limit
on the CBC call so that a width that does not finish is recorded as "unresolved" rather
than running on.  The maximum blackout is the number of grid points minus the minimum
hitting set.  The kept set of the ILP solution is turned into the blackout and rechecked
with verify_narrow.collision.

Coordinates in the JSON output are ONE-BASED (column, row), (1, 1) top left.

Usage:
  python five_row_cbc.py --widths 8 9 --cap 1800 --out ../data/five_row_cbc.json
"""
import argparse
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, REPO)
import pulp  # noqa: E402
import verify_narrow  # noqa: E402
from solver.enumerate import grid_points, rectangles  # noqa: E402
from solver.table import difference_table, prune  # noqa: E402

H = 5


def solve_width(m, cap):
    t0 = time.time()
    pts = grid_points(H, m)
    idx = {p: k for k, p in enumerate(pts)}
    rects = rectangles(H, m)
    pruned = prune(difference_table(rects))
    row_masks = [sum(1 << idx[p] for p in r) for r in pruned]
    t_build = time.time() - t0
    prob = pulp.LpProblem('min_hitting_set', pulp.LpMinimize)
    x = [pulp.LpVariable(f'x{k}', cat='Binary') for k in range(len(pts))]
    prob += pulp.lpSum(x)
    for mask in row_masks:
        prob += pulp.lpSum(x[k] for k in range(len(pts)) if mask >> k & 1) >= 1
    t1 = time.time()
    status = prob.solve(pulp.PULP_CBC_CMD(msg=False, timeLimit=cap))
    t_solve = time.time() - t1
    result = dict(width=m, solver='CBC (PuLP %s)' % pulp.__version__,
                  rectangles=len(rects), pruned_rows=len(row_masks),
                  variables=len(pts), constraints=len(row_masks),
                  build_seconds=round(t_build, 1), solve_seconds=round(t_solve, 1),
                  pulp_status=pulp.LpStatus[status], cap_seconds=cap)
    if pulp.LpStatus[status] == 'Optimal' and t_solve < cap - 1:
        kept = [pts[k] for k in range(len(pts)) if pulp.value(x[k]) > 0.5]
        black = [p for p in pts if p not in set(kept)]
        result['status'] = 'optimal'
        result['max_blackout'] = len(pts) - len(kept)
        result['witness_one_based'] = [list(p) for p in black]
        zero = [(c - 1, r - 1) for c, r in black]
        result['witness_valid_by_verify_narrow'] = \
            verify_narrow.collision(verify_narrow.rectangles(H, m),
                                    verify_narrow.mask(zero, m)) is None
    else:
        result['status'] = 'unresolved'
        try:
            result['incumbent_blackout'] = len(pts) - int(round(pulp.value(prob.objective)))
        except Exception:
            pass
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--widths', type=int, nargs='+', default=[8, 9])
    ap.add_argument('--cap', type=int, default=1800)
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    results = dict(method='minimum hitting set ILP, CBC through PuLP (solver/engine.py pipeline)',
                   coordinates='one-based (column,row)', instances=[])
    for m in args.widths:
        r = solve_width(m, args.cap)
        results['instances'].append(r)
        print(f"width {m}: {r['status']} max_blackout {r.get('max_blackout')} "
              f"solve {r['solve_seconds']}s rows {r['pruned_rows']} "
              f"valid {r.get('witness_valid_by_verify_narrow')}", flush=True)
        if args.out:
            with open(args.out, 'w') as f:
                json.dump(results, f, indent=1)


if __name__ == '__main__':
    main()
