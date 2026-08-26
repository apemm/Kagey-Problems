"""Minimum hitting set -> maximum blackout. OWNER: Arjun.

max_blackout(rows, cols, count_witnesses=True) -> (max blackout size, number of maximum blackouts)

Pipeline: enumerate.rectangles -> table.difference_table -> table.prune -> minimum hitting
set of the pruned rows by ILP (PuLP / CBC). The maximum blackout is |V| minus the minimum
hitting set size (PROBLEM.md convention 4). Witnesses are counted by exhaustive enumeration
of all kept sets of the minimum size, checked against the pruned rows with bitmasks; that
count is exact and independent of the ILP's particular optimum. With count_witnesses=False
the second component is None.
"""
from itertools import combinations

import pulp

from solver.enumerate import grid_points, rectangles
from solver.table import difference_table, prune


def _solver():
    """CBC bundled with PuLP; COIN_CMD is the non-deprecated entry point when available."""
    try:
        cmd = pulp.COIN_CMD(msg=False)
        if cmd.available():
            return cmd
    except Exception:
        pass
    return pulp.PULP_CBC_CMD(msg=False)


def _min_hitting_set_size(n_points, row_masks):
    if not row_masks:
        return 0
    prob = pulp.LpProblem("min_hitting_set", pulp.LpMinimize)
    x = [pulp.LpVariable(f"x{k}", cat="Binary") for k in range(n_points)]
    prob += pulp.lpSum(x)
    for m in row_masks:
        prob += pulp.lpSum(x[k] for k in range(n_points) if m >> k & 1) >= 1
    status = prob.solve(_solver())
    if pulp.LpStatus[status] != "Optimal":
        raise RuntimeError(f"ILP did not solve to optimality: {pulp.LpStatus[status]}")
    return int(round(pulp.value(prob.objective)))


def _count_hitting_sets(n_points, row_masks, size):
    count = 0
    for K in combinations(range(n_points), size):
        kmask = 0
        for b in K:
            kmask |= 1 << b
        if all(m & kmask for m in row_masks):
            count += 1
    return count


def max_blackout(rows, cols, count_witnesses=True):
    pts = grid_points(rows, cols)
    idx = {p: k for k, p in enumerate(pts)}
    n = len(pts)
    rects = rectangles(rows, cols)
    pruned = prune(difference_table(rects))
    row_masks = [sum(1 << idx[p] for p in r) for r in pruned]
    h = _min_hitting_set_size(n, row_masks)
    witnesses = _count_hitting_sets(n, row_masks, h) if count_witnesses else None
    return n - h, witnesses


if __name__ == "__main__":
    import sys
    import time
    grids = [tuple(int(x) for x in a.lower().split("x")) for a in sys.argv[1:]] or \
        [(2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (4, 4)]
    print("| grid (rows x cols) | rectangles | pruned rows | max blackout | # maximum blackouts | time |")
    print("|---|---|---|---|---|---|")
    for r, c in grids:
        t0 = time.time()
        rects = rectangles(r, c)
        nrows = len(prune(difference_table(rects)))
        v, w = max_blackout(r, c)
        print(f"| {r} x {c} | {len(rects)} | {nrows} | {v} | {w} | {time.time()-t0:.2f}s |", flush=True)
