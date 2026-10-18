"""Independent SAT check of "there is a valid blackout of at least k points on an
h x m grid".

Encoding (written from scratch): one Boolean per grid point (black), one clause
per inclusion-minimal symmetric difference of two distinct rectangles ("not all
of it black"), rectangles from the right-angle-triple enumerator, minimality by
submask enumeration, cardinality "at least k" by the k-modulo totalizer of
pysat.  Optional row split: case j means rows 1..j-1 carry at most two black
points and row j at least three (a different split from the column split of
small_cells_split.py).

Single run:  python cells_sat_check.py run ROWS COLS BOUND SOLVER OUT.json [ROWCASE]
Batch:       python cells_sat_check.py batch JOBS.json CONCURRENCY CAP_SECONDS [--overwrite]
  JOBS.json is a list of [rows, cols, bound, solver, out, rowcase_or_null].
Each batch job runs in its own process and is killed at the cap; a killed job is
recorded as "unresolved", a failed or rejected job as "error".  A result is accepted
only after a successful exit and a check of a fresh attempt file (see batch_jobs.py);
the batch exits nonzero unless every job ended SAT or UNSAT.  Without --overwrite a batch
refuses to start (exit code 3) when the output path of some job already exists.  A single run writes its
output atomically.  Coordinates in the output are one-based (column,row).
"""
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cells_common_check import rectangles_by_triples, first_collision  # noqa: E402
import batch_jobs  # noqa: E402

INPUTS = ['cells_sat_check.py', 'cells_common_check.py']


def minimal_differences(rects_masks):
    diffs = set()
    n = len(rects_masks)
    for i in range(n):
        a = rects_masks[i]
        for j in range(i + 1, n):
            diffs.add(a ^ rects_masks[j])
    minimal = []
    for d in diffs:
        sub = (d - 1) & d
        keep = True
        while sub:
            if sub in diffs:
                keep = False
                break
            sub = (sub - 1) & d
        if keep:
            minimal.append(d)
    return len(diffs), minimal


def run(rows, cols, bound, solver_name, out, rowcase=None, job_key=None):
    from pysat.card import CardEnc, EncType
    from pysat.solvers import Solver
    import pysat
    t0 = time.time()
    points = [(c, r) for r in range(1, rows + 1) for c in range(1, cols + 1)]
    var = {p: i + 1 for i, p in enumerate(points)}
    rects = rectangles_by_triples(rows, cols)
    masks = [sum(1 << (var[p] - 1) for p in rect) for rect in rects]
    ndiff, minimal = minimal_differences(masks)
    clauses = []
    for d in minimal:
        clauses.append([-(i + 1) for i in range(rows * cols) if d >> i & 1])
    top = rows * cols
    card = CardEnc.atleast(lits=list(range(1, top + 1)), bound=bound, top_id=top, encoding=EncType.kmtotalizer)
    clauses.extend(card.clauses)
    top = max(top, card.nv)
    if rowcase is not None:
        for r in range(1, rowcase):
            lits = [var[(c, r)] for c in range(1, cols + 1)]
            cnf = CardEnc.atmost(lits=lits, bound=2, top_id=top, encoding=EncType.seqcounter)
            clauses.extend(cnf.clauses)
            top = max(top, cnf.nv)
        lits = [var[(c, rowcase)] for c in range(1, cols + 1)]
        cnf = CardEnc.atleast(lits=lits, bound=3, top_id=top, encoding=EncType.seqcounter)
        clauses.extend(cnf.clauses)
        top = max(top, cnf.nv)
    encode = time.time() - t0
    t1 = time.time()
    with Solver(name=solver_name, bootstrap_with=clauses) as s:
        sat = s.solve()
        model = s.get_model() if sat else None
    solve = time.time() - t1
    result = {'rows': rows, 'cols': cols, 'bound': bound, 'rowcase': rowcase,
              'method': 'SAT, minimal-difference clauses, kmtotalizer at-least, right-angle-triple rectangles',
              'solver': solver_name, 'pysat_version': pysat.__version__,
              'rectangles': len(rects), 'distinct_differences': ndiff, 'minimal_differences': len(minimal),
              'variables': top, 'clauses': len(clauses),
              'status': 'SAT' if sat else 'UNSAT', 'encode_seconds': round(encode, 1),
              'solve_seconds': round(solve, 1), 'coordinates': 'one-based (column,row), (1,1) top-left'}
    if sat:
        black = [p for p in points if model[var[p] - 1] > 0]
        result['witness'] = black
        result['witness_size'] = len(black)
        result['witness_valid_by_triples'] = first_collision(rects, set(black)) is None
    result['job_key'] = job_key
    result['input_sha256'] = batch_jobs.input_hashes(INPUTS)
    result['complete'] = True
    batch_jobs.atomic_write_json(out, result)
    print(json.dumps({k: v for k, v in result.items() if k != 'witness'}))


def describe(job):
    rows, cols, bound, solver, out, rowcase = job
    params = {'rows': rows, 'cols': cols, 'bound': bound, 'rowcase': rowcase, 'solver': solver}
    return params, out, [rows, cols, bound, solver], ([] if rowcase is None else [rowcase])


def check(res):
    if res['status'] == 'SAT':
        if res.get('witness_valid_by_triples') is not True:
            return 'SAT witness not valid'
        if not isinstance(res.get('witness_size'), int) or res['witness_size'] < res['bound']:
            return 'SAT witness smaller than the bound'
    return None


def batch(jobs_path, concurrency, cap, overwrite=False):
    return batch_jobs.run_batch('cells_sat_check.py', jobs_path, concurrency, cap,
                                describe, INPUTS, check, overwrite=overwrite)


if __name__ == '__main__':
    argv = sys.argv[1:]
    key = batch_jobs.pop_job_key(argv)
    if argv[0] == 'run':
        rows, cols, bound = map(int, argv[1:4])
        solver, out = argv[4], argv[5]
        rowcase = int(argv[6]) if len(argv) > 6 else None
        run(rows, cols, bound, solver, out, rowcase, key)
    else:
        jobs_path, concurrency, cap, overwrite = batch_jobs.batch_args(argv)
        sys.exit(batch(jobs_path, concurrency, cap, overwrite))
