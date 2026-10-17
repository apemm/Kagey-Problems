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
Batch:       python six_row_sat_check.py batch JOBS.json CONCURRENCY CAP_SECONDS
  JOBS.json is a list of [width, partition_index, solver, out].
Output coordinates are one-based (column, row), (1,1) top left.
"""
import json
import os
import subprocess
import sys
import time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cells_common_check import rectangles_by_triples, first_collision  # noqa: E402
from six_row_dfs_check import partitions  # noqa: E402

ROWS = 6


def run(width, idx, solver_name, out):
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
    result = {'rows': ROWS, 'width': width, 'target': width + 9,
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
    json.dump(result, open(out, 'w'), indent=1)
    print(json.dumps({k: v for k, v in result.items() if k != 'witness'}))


def batch(jobs_path, concurrency, cap):
    jobs = json.load(open(jobs_path))
    pending = list(jobs)
    running = []
    summary = []
    while pending or running:
        while pending and len(running) < concurrency:
            job = pending.pop(0)
            width, idx, solver, out = job
            args = [sys.executable, os.path.abspath(__file__), 'run', str(width), str(idx), solver, out]
            log = open(out + '.log', 'w')
            p = subprocess.Popen(args, stdout=log, stderr=subprocess.STDOUT)
            running.append((job, p, time.time(), log))
        time.sleep(5)
        still = []
        for job, p, start, log in running:
            rc = p.poll()
            elapsed = time.time() - start
            if rc is None and elapsed > cap:
                p.kill()
                p.wait()
                log.close()
                width, idx, solver, out = job
                json.dump({'rows': ROWS, 'width': width, 'partition_index': idx, 'solver': solver,
                           'status': 'unresolved', 'cap_seconds': cap, 'wall_seconds': round(elapsed, 1),
                           'note': 'process killed at the cap'}, open(out, 'w'), indent=1)
                summary.append([job, 'unresolved', round(elapsed, 1)])
                print('killed', job, round(elapsed, 1), flush=True)
            elif rc is None:
                still.append((job, p, start, log))
            else:
                log.close()
                try:
                    status = json.load(open(job[3]))['status']
                except Exception:
                    status = 'error rc=%s' % rc
                summary.append([job, status, round(elapsed, 1)])
                print('done', job, status, round(elapsed, 1), flush=True)
        running = still
    json.dump(summary, open(jobs_path.replace('.json', '_summary.json'), 'w'), indent=1)


if __name__ == '__main__':
    if sys.argv[1] == 'run':
        run(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5])
    else:
        batch(sys.argv[2], int(sys.argv[3]), float(sys.argv[4]))
