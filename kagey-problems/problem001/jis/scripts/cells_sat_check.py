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
Batch:       python cells_sat_check.py batch JOBS.json CONCURRENCY CAP_SECONDS
  JOBS.json is a list of [rows, cols, bound, solver, out, rowcase_or_null].
Each batch job runs in its own process and is killed at the cap; a killed job is
recorded as "unresolved".  Coordinates in the output are one-based (column,row).
"""
import json
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cells_common_check import rectangles_by_triples, first_collision  # noqa: E402


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


def run(rows, cols, bound, solver_name, out, rowcase=None):
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
            rows, cols, bound, solver, out, rowcase = job
            args = [sys.executable, os.path.abspath(__file__), 'run', str(rows), str(cols), str(bound), solver, out]
            if rowcase is not None:
                args.append(str(rowcase))
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
                rows, cols, bound, solver, out, rowcase = job
                json.dump({'rows': rows, 'cols': cols, 'bound': bound, 'rowcase': rowcase, 'solver': solver,
                           'status': 'unresolved', 'cap_seconds': cap, 'wall_seconds': round(elapsed, 1),
                           'note': 'process killed at the cap'}, open(out, 'w'), indent=1)
                summary.append([job, 'unresolved', round(elapsed, 1)])
                print('killed', job, round(elapsed, 1), flush=True)
            elif rc is None:
                still.append((job, p, start, log))
            else:
                log.close()
                try:
                    status = json.load(open(job[4]))['status']
                except Exception:
                    status = 'error rc=%s' % rc
                summary.append([job, status, round(elapsed, 1)])
                print('done', job, status, round(elapsed, 1), flush=True)
        running = still
    json.dump(summary, open(jobs_path.replace('.json', '_summary.json'), 'w'), indent=1)


if __name__ == '__main__':
    if sys.argv[1] == 'run':
        rows, cols, bound = map(int, sys.argv[2:5])
        solver, out = sys.argv[5], sys.argv[6]
        rowcase = int(sys.argv[7]) if len(sys.argv) > 7 else None
        run(rows, cols, bound, solver, out, rowcase)
    else:
        batch(sys.argv[2], int(sys.argv[3]), float(sys.argv[4]))
