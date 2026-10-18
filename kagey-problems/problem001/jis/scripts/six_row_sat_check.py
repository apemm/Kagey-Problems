"""Independent structured SAT check for six-row blackouts of m+9 points.

Encoding (written from scratch, point variables rather than column types or
edge-at-column variables): one Boolean per grid point; every column has at least
one and at most two black points; two black points in a column may not lie on
the same side of the row partition; nine edge indicators per column, each
equivalent to "both ends black in this column", and every K_{3,3} edge is used
in exactly one column; one clause per symmetric difference of two rectangles
("not all black"), rectangles from the right-angle-triple enumerator, after
dropping differences the column constraints already satisfy and differences
that contain a smaller difference reachable by deleting one or two points.

Single run:  python six_row_sat_check.py run WIDTH PARTITION_INDEX SOLVER OUT.json
Batch:       python six_row_sat_check.py batch JOBS.json CONCURRENCY CAP_SECONDS [--overwrite]
  JOBS.json is a list of [width, partition_index, solver, out].
Each batch job runs in its own process and is killed at the cap; a killed job is
recorded as "unresolved", a failed or rejected job as "error".  A result is accepted
only after a successful exit and a check of a fresh attempt file (see batch_jobs.py);
the batch exits nonzero unless every job ended SAT or UNSAT.  Without --overwrite a batch
refuses to start (exit code 3) when the output path of some job already exists.  A single run writes its
output atomically.  Output coordinates are one-based (column, row), (1,1) top left.
"""
import json
import os
import sys
import time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cells_common_check import rectangles_by_triples, first_collision  # noqa: E402
from six_row_dfs_check import partitions  # noqa: E402
import batch_jobs  # noqa: E402

INPUTS = ['six_row_sat_check.py', 'cells_common_check.py', 'six_row_dfs_check.py']

ROWS = 6


def run(width, idx, solver_name, out, job_key=None):
    from pysat.card import CardEnc, EncType
    from pysat.solvers import Solver
    import pysat
    t0 = time.time()
    a, b = partitions()[idx]
    edges = [(x, y) if x < y else (y, x) for x in a for y in b]
    var = lambda c, r: (c - 1) * ROWS + r
    npts = width * ROWS
    clauses = []
    same_side = [tuple(sorted(p)) for side in (a, b) for p in combinations(side, 2)]
    for c in range(1, width + 1):
        clauses.append([var(c, r) for r in range(1, ROWS + 1)])
        for t in combinations(range(1, ROWS + 1), 3):
            clauses.append([-var(c, r) for r in t])
        for x, y in same_side:
            clauses.append([-var(c, x), -var(c, y)])
    top = npts
    edge_vars = {}
    for i, (x, y) in enumerate(edges):
        for c in range(1, width + 1):
            top += 1
            e = top
            edge_vars[c, i] = e
            clauses.append([-e, var(c, x)])
            clauses.append([-e, var(c, y)])
            clauses.append([-var(c, x), -var(c, y), e])
        cnf = CardEnc.equals(lits=[edge_vars[c, i] for c in range(1, width + 1)], bound=1,
                             top_id=top, encoding=EncType.seqcounter)
        clauses.extend(cnf.clauses)
        top = max(top, cnf.nv)
    structural = len(clauses)

    rects = rectangles_by_triples(ROWS, width)
    masks = [sum(1 << (var(c, r) - 1) for c, r in rect) for rect in rects]
    diffs = set()
    for i in range(len(masks)):
        m = masks[i]
        for j in range(i + 1, len(masks)):
            diffs.add(m ^ masks[j])
    colmask = (1 << ROWS) - 1
    same_side_masks = [(1 << (x - 1)) | (1 << (y - 1)) for x, y in same_side]

    def trivially_true(d):
        for c in range(width):
            col = (d >> (c * ROWS)) & colmask
            if col.bit_count() >= 3:
                return True
            if col.bit_count() == 2 and col in same_side_masks:
                return True
        return False

    kept = []
    for d in diffs:
        if trivially_true(d):
            continue
        bits = [i for i in range(npts) if d >> i & 1]
        drop = False
        for k in (1, 2):
            for rem in combinations(bits, k):
                s = d
                for i in rem:
                    s &= ~(1 << i)
                if s in diffs:
                    drop = True
                    break
            if drop:
                break
        if not drop:
            kept.append(d)
    for d in kept:
        clauses.append([-(i + 1) for i in range(npts) if d >> i & 1])
    encode = time.time() - t0
    t1 = time.time()
    with Solver(name=solver_name, bootstrap_with=clauses) as s:
        sat = s.solve()
        model = s.get_model() if sat else None
    solve = time.time() - t1
    result = {'rows': ROWS, 'width': width, 'target': width + 9, 'partition_index': idx,
              'partition_one_based_rows': [list(a), list(b)],
              'method': 'structured SAT, point variables, column constraints, edge indicators, difference clauses',
              'solver': solver_name, 'pysat_version': pysat.__version__,
              'rectangles': len(rects), 'distinct_differences': len(diffs), 'difference_clauses': len(kept),
              'structural_clauses': structural, 'variables': top, 'clauses': len(clauses),
              'status': 'SAT' if sat else 'UNSAT', 'encode_seconds': round(encode, 1),
              'solve_seconds': round(solve, 1), 'coordinates': 'one-based (column,row), (1,1) top-left'}
    if sat:
        black = [(c, r) for c in range(1, width + 1) for r in range(1, ROWS + 1) if model[var(c, r) - 1] > 0]
        result['witness'] = black
        result['witness_size'] = len(black)
        result['witness_valid_by_triples'] = first_collision(rects, set(black)) is None
    result['job_key'] = job_key
    result['input_sha256'] = batch_jobs.input_hashes(INPUTS)
    result['complete'] = True
    batch_jobs.atomic_write_json(out, result)
    print(json.dumps({k: v for k, v in result.items() if k != 'witness'}))


def describe(job):
    width, idx, solver, out = job
    params = {'rows': ROWS, 'width': width, 'partition_index': idx, 'solver': solver}
    return params, out, [width, idx, solver], []


def check(res):
    if res['status'] == 'SAT':
        if res.get('witness_valid_by_triples') is not True:
            return 'SAT witness not valid'
        if res.get('witness_size') != res['width'] + 9:
            return 'SAT witness does not have width + 9 points'
    return None


def batch(jobs_path, concurrency, cap, overwrite=False):
    return batch_jobs.run_batch('six_row_sat_check.py', jobs_path, concurrency, cap,
                                describe, INPUTS, check, overwrite=overwrite)


if __name__ == '__main__':
    argv = sys.argv[1:]
    key = batch_jobs.pop_job_key(argv)
    if argv[0] == 'run':
        run(int(argv[1]), int(argv[2]), argv[3], argv[4], key)
    else:
        jobs_path, concurrency, cap, overwrite = batch_jobs.batch_args(argv)
        sys.exit(batch(jobs_path, concurrency, cap, overwrite))
