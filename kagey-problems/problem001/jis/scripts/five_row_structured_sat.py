r"""Five rows, structured SAT search for a blackout of m+6 points (method A).

Every valid blackout of a 5 x m grid with m+6 points has the equality structure of the
row bound: every column is black in exactly one row or in exactly the two rows of one
edge of a complete bipartite graph K_{2,3} on the five rows, and each of the six edges
is used in exactly one column.  For each of the ten 2+3 partitions of the rows this
script builds one SAT instance (pysat) with

  * a point variable per grid point,
  * the column structure above (singleton or edge double, each edge once),
  * one clause per symmetric difference D of two distinct rectangles saying that D is
    not entirely black, restricted to the differences that the column structure allows
    and with supersets of smaller differences dropped.

A satisfying assignment is a blackout of m+6 points; it is rechecked against every
rectangle with verify_narrow.collision.  "Unsatisfiable" for all ten partitions proves
that no blackout of m+6 points exists at that width.

Every instance is solved in a child process with a hard wall-clock cap, so a run that
exceeds the cap is recorded as "unresolved" instead of hanging.

Rectangles come from verify_narrow.rectangles (equal diagonals, same midpoint), with
point (x, y) stored at bit y*m + x, x the zero-based column and y the zero-based row.
All coordinates in the JSON output are ONE-BASED (column, row), (1, 1) top left.

Usage:
  python five_row_structured_sat.py --widths 8 9 10 --solver cadical153 --cap 1800
                                    --out ../data/five_row_structured_cadical153.json
Optional: --partitions 12 13 ... (one-based row pairs forming the 2-set), --count N
(enumerate up to N optima per width with blocking clauses, only where the instance is
satisfiable), --no-prune (keep superset differences).
"""
import argparse
import json
import os
import subprocess
import sys
import time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, REPO)
import verify_narrow  # noqa: E402

ROWS = 5
PARTITIONS = [pair for pair in combinations(range(ROWS), 2)]   # the 2-set, zero-based


def column_masks(m):
    return [sum(1 << (y * m + x) for y in range(ROWS)) for x in range(m)]


def differences(rects):
    """All distinct symmetric differences of two distinct rectangles (bitmasks)."""
    out = set()
    for a, b in combinations(rects, 2):
        out.add(a ^ b)
    return out


def structure_feasible(d, m, edge_set):
    """Can D be entirely black under the column structure of the given partition?"""
    for x in range(m):
        rows = [y for y in range(ROWS) if d >> (y * m + x) & 1]
        if len(rows) >= 3:
            return False
        if len(rows) == 2 and (rows[0], rows[1]) not in edge_set:
            return False
    return True


def prune_supersets(masks):
    """Drop every mask that strictly contains another mask of the family."""
    by_size = sorted(masks, key=lambda d: d.bit_count())
    kept = set()
    kept_sizes = set()
    result = []
    for d in by_size:
        size = d.bit_count()
        bits = [1 << i for i in range(d.bit_length()) if d >> i & 1]
        redundant = False
        for s in sorted(kept_sizes):
            if s >= size:
                break
            for sub in combinations(bits, s):
                if sum(sub) in kept:
                    redundant = True
                    break
            if redundant:
                break
        if not redundant:
            kept.add(d)
            kept_sizes.add(size)
            result.append(d)
    return result


def build_instance(m, part, prune=True):
    """CNF for one partition.  part = tuple of 2 zero-based rows (the 2-set)."""
    other = tuple(r for r in range(ROWS) if r not in part)
    edges = [tuple(sorted((p, q))) for p in part for q in other]
    edge_set = set(edges)
    rects = verify_narrow.rectangles(ROWS, m)
    diffs = differences(rects)
    feasible = [d for d in diffs if structure_feasible(d, m, edge_set)]
    kept = prune_supersets(feasible) if prune else feasible

    def x(col, row):
        return col * ROWS + row + 1

    def y(e, col):
        return ROWS * m + e * m + col + 1

    clauses = []
    for c in range(m):
        clauses.append([x(c, r) for r in range(ROWS)])                      # nonempty
        for a, b, d in combinations(range(ROWS), 3):                        # at most two
            clauses.append([-x(c, a), -x(c, b), -x(c, d)])
        for a, b in combinations(range(ROWS), 2):                           # doubles are edges
            if (a, b) in edge_set:
                clauses.append([-x(c, a), -x(c, b), y(edges.index((a, b)), c)])
            else:
                clauses.append([-x(c, a), -x(c, b)])
        for e, (a, b) in enumerate(edges):                                  # edge var -> both black
            clauses.append([-y(e, c), x(c, a)])
            clauses.append([-y(e, c), x(c, b)])
            for r in range(ROWS):
                if r not in (a, b):
                    clauses.append([-y(e, c), -x(c, r)])
        for e, f in combinations(range(len(edges)), 2):                     # one edge per column
            clauses.append([-y(e, c), -y(f, c)])
    for e in range(len(edges)):                                             # each edge once
        clauses.append([y(e, c) for c in range(m)])
        for c, d in combinations(range(m), 2):
            clauses.append([-y(e, c), -y(e, d)])
    structural = len(clauses)
    for d in kept:
        clauses.append([-x(i % m, i // m) for i in range(d.bit_length()) if d >> i & 1])
    info = dict(rectangles=len(rects), differences=len(diffs), feasible=len(feasible),
                kept=len(kept), structural_clauses=structural, clauses=len(clauses),
                variables=ROWS * m + len(edges) * m, edges=edges)
    return clauses, info, rects


def decode(model, m):
    """Black points (col, row), zero-based, from a model of the point variables."""
    return sorted(((v - 1) // ROWS, (v - 1) % ROWS) for v in model if 0 < v <= ROWS * m)


def worker(args):
    from pysat.solvers import Solver
    m, part = args.width, tuple(args.partition)
    t0 = time.time()
    clauses, info, rects = build_instance(m, part, prune=not args.no_prune)
    t_build = time.time() - t0
    t1 = time.time()
    models = []
    with Solver(name=args.solver, bootstrap_with=clauses) as s:
        sat = s.solve()
        if sat:
            model = s.get_model()
            pts = decode(model, m)
            models.append(pts)
            if args.count:
                while len(models) < args.count:
                    s.add_clause([-(c * ROWS + r + 1) for c, r in pts] +
                                 [c * ROWS + r + 1 for c in range(m) for r in range(ROWS)
                                  if (c, r) not in set(pts)])
                    if not s.solve():
                        break
                    pts = decode(s.get_model(), m)
                    models.append(pts)
    t_solve = time.time() - t1
    result = dict(width=m, partition_rows_one_based=[r + 1 for r in part], solver=args.solver,
                  status='SAT' if sat else 'UNSAT', build_seconds=round(t_build, 2),
                  solve_seconds=round(t_solve, 2), **info)
    if sat:
        pts = models[0]
        black = verify_narrow.mask(pts, m)
        col = verify_narrow.collision(rects, black)
        assert len(pts) == m + 6, len(pts)
        result['witness_one_based'] = [[c + 1, r + 1] for c, r in pts]
        result['witness_valid_by_verify_narrow'] = col is None
        result['witness_picture'] = [''.join('#' if (c, r) in set(pts) else '.'
                                             for c in range(m)) for r in range(ROWS)]
        if args.count:
            result['models_found'] = len(models)
            result['count_exhausted'] = len(models) < args.count
            bad = [p for p in models
                   if verify_narrow.collision(rects, verify_narrow.mask(p, m)) is not None]
            result['models_failing_recheck'] = len(bad)
            result['models_one_based'] = [[[c + 1, r + 1] for c, r in p] for p in models]
    print(json.dumps(result))


def run_instance(args, m, part):
    cmd = [sys.executable, '-I', os.path.abspath(__file__), '--worker', '--width', str(m),
           '--partition', *map(str, part), '--solver', args.solver]
    if args.no_prune:
        cmd.append('--no-prune')
    if args.count:
        cmd += ['--count', str(args.count)]
    t0 = time.time()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=args.cap)
    except subprocess.TimeoutExpired:
        return dict(width=m, partition_rows_one_based=[r + 1 for r in part],
                    solver=args.solver, status='unresolved',
                    wall_seconds=round(time.time() - t0, 1), cap_seconds=args.cap)
    wall = time.time() - t0
    if proc.returncode != 0:
        return dict(width=m, partition_rows_one_based=[r + 1 for r in part],
                    solver=args.solver, status='error', wall_seconds=round(wall, 1),
                    stderr=proc.stderr[-2000:])
    out = json.loads(proc.stdout.strip().splitlines()[-1])
    out['wall_seconds'] = round(wall, 1)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--widths', type=int, nargs='+', default=list(range(8, 21)))
    ap.add_argument('--partitions', nargs='*', default=None,
                    help='one-based two-digit row pairs, e.g. 12 13 (the 2-set)')
    ap.add_argument('--solver', default='cadical153')
    ap.add_argument('--cap', type=int, default=1800)
    ap.add_argument('--count', type=int, default=0)
    ap.add_argument('--no-prune', action='store_true')
    ap.add_argument('--out', default=None)
    ap.add_argument('--worker', action='store_true')
    ap.add_argument('--width', type=int)
    ap.add_argument('--partition', type=int, nargs=2)
    args = ap.parse_args()
    if args.worker:
        worker(args)
        return
    import pysat
    parts = PARTITIONS
    if args.partitions:
        parts = [tuple(int(ch) - 1 for ch in p) for p in args.partitions]
    results = dict(method='structured SAT per 2+3 row partition (method A)',
                   solver=args.solver, pysat_version=pysat.__version__,
                   python_version=sys.version.split()[0], cap_seconds=args.cap,
                   superset_pruning=not args.no_prune, coordinates='one-based (column,row)',
                   instances=[], summary={})
    for m in args.widths:
        statuses = []
        for part in parts:
            r = run_instance(args, m, part)
            results['instances'].append(r)
            statuses.append(r['status'])
            print(f"width {m} partition {[p + 1 for p in part]}: {r['status']} "
                  f"wall {r.get('wall_seconds')}s clauses {r.get('clauses')} "
                  f"vars {r.get('variables')}", flush=True)
            if args.out:
                with open(args.out, 'w') as f:
                    json.dump(results, f, indent=1)
        if any(s == 'SAT' for s in statuses):
            verdict = 'm+6 attained'
        elif all(s == 'UNSAT' for s in statuses):
            verdict = 'no blackout of m+6 points (all partitions UNSAT)'
        else:
            verdict = 'unresolved'
        results['summary'][str(m)] = dict(verdict=verdict, statuses=statuses)
        print(f"== width {m}: {verdict}", flush=True)
        if args.out:
            with open(args.out, 'w') as f:
                json.dump(results, f, indent=1)


if __name__ == '__main__':
    main()
