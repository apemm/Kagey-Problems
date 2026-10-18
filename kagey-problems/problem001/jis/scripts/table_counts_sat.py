"""Count the maximum blackouts a_h(m) of small grids by SAT model enumeration.

This is the first of two routes for the missing entries of A399580. The clauses are encoding A
of small_cells_sat.py (rectangles from verify_narrow.rectangles, one clause per inclusion-minimal
symmetric difference of two rectangles), with the size fixed to exactly k = f(h,m) by a
sequential counter. After each model we add the clause "not all of these k points black", which
blocks that model and nothing else, since every model has exactly k points. The solver is
glucose4, so the wall-clock cap of 30 minutes can interrupt a single call, and the cap is also
checked between models.

Every model is rechecked by verify_narrow.collision and must have exactly k points. The count is
reported as exact only when the solver ends with UNSAT. A run that hits the cap is reported as
unresolved, with the number of models found so far as a lower bound.

With --split N the cell is cut into one part for each possible content of the first column,
fixed by unit clauses, and the parts run on N processes with a cap of 30 minutes each. The count
is exact only when every part ends with UNSAT.

Usage: python table_counts_sat.py 5x6@11 5x7@12 ...   (results go to the file named by --out,
default jis/data/table_counts_sat.json). Coordinates in the output are one-based (column,row)
with (1,1) top-left.
"""
import hashlib
import json
import os
import sys
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)

import pysat
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

from verify_narrow import collision, rectangles
from small_cells_sat import bits, minimal_differences, points_one_based

CAP_SECONDS = 1800
SOLVER = 'glucose4'


def digest(models):
    """SHA-256 of the sorted list of models, each a sorted list of one-based (column,row)."""
    text = json.dumps(sorted([list(p) for p in m] for m in models))
    return hashlib.sha256(text.encode()).hexdigest()


def count_cell(rows, cols, k, cap=CAP_SECONDS, keep=20, first=None):
    rects = rectangles(rows, cols)
    n = rows * cols
    kept, _ = minimal_differences(rects)
    clauses = [[-(i + 1) for i in bits(d)] for d in kept]
    card = CardEnc.equals(lits=list(range(1, n + 1)), bound=k, top_id=n,
                          encoding=EncType.seqcounter)
    clauses += card.clauses
    if first is not None:                      # fix column 1: bit y of first is row y+1
        clauses += [[(y * cols + 1) if first >> y & 1 else -(y * cols + 1)]
                    for y in range(rows)]
    t0 = time.time()
    found = []
    status = 'exact'
    with Solver(name=SOLVER, bootstrap_with=clauses) as s:
        while True:
            left = cap - (time.time() - t0)
            if left <= 0:
                status = 'unresolved'
                break
            timer = threading.Timer(left, s.interrupt)
            timer.start()
            try:
                r = s.solve_limited(expect_interrupt=True)
            finally:
                timer.cancel()
            if r is None:
                status = 'unresolved'
                break
            if r is False:
                break
            model = s.get_model()
            black = sum(1 << (v - 1) for v in model if 0 < v <= n)
            assert black.bit_count() == k, (rows, cols, black)
            assert collision(rects, black) is None, (rows, cols, black)
            found.append(black)
            s.add_clause([-(i + 1) for i in bits(black)])
            s.clear_interrupt()
    dt = time.time() - t0
    assert len(set(found)) == len(found)
    return {'grid': f'{rows}x{cols}', 'rows': rows, 'cols': cols, 'size': k,
            'first_column': first, 'all': [points_one_based(b, cols) for b in found],
            'solver': SOLVER, 'pysat_version': pysat.__version__,
            'rectangles': len(rects), 'minimal_differences': len(kept),
            'status': status, 'count': len(found) if status == 'exact' else None,
            'models_found': len(found), 'seconds': round(dt, 2),
            'all_models_valid_by_verify_narrow': True,
            'coordinates': 'one-based (column,row), (1,1) top-left',
            'models_sha256': digest([points_one_based(b, cols) for b in found]),
            'first_models': sorted(points_one_based(b, cols) for b in found)[:keep]}


def _part(job):
    return count_cell(*job)


def count_split(rows, cols, k, workers):
    from multiprocessing import Pool
    jobs = [(rows, cols, k, CAP_SECONDS, 20, s) for s in range(1 << rows)
            if bin(s).count('1') <= k]
    with Pool(workers) as pool:
        parts = pool.map(_part, jobs, chunksize=1)
    models = sorted(m for p in parts for m in p['all'])
    exact = all(p['status'] == 'exact' for p in parts)
    return {'grid': f'{rows}x{cols}', 'rows': rows, 'cols': cols, 'size': k,
            'solver': SOLVER, 'pysat_version': pysat.__version__,
            'split': 'by first column', 'parts': len(parts),
            'parts_unresolved': [p['first_column'] for p in parts if p['status'] != 'exact'],
            'status': 'exact' if exact else 'unresolved',
            'count': len(models) if exact else None, 'models_found': len(models),
            'seconds_max_part': max(p['seconds'] for p in parts),
            'seconds_total': round(sum(p['seconds'] for p in parts), 2),
            'all_models_valid_by_verify_narrow': True,
            'coordinates': 'one-based (column,row), (1,1) top-left',
            'models_sha256': digest(models), 'first_models': models[:20], 'all': models}


def main():
    args = sys.argv[1:]
    out = os.path.join(ROOT, 'jis', 'data', 'table_counts_sat.json')
    if '--out' in args:
        i = args.index('--out')
        out = args[i + 1]
        del args[i:i + 2]
    workers = 0
    if '--split' in args:
        i = args.index('--split')
        workers = int(args[i + 1])
        del args[i:i + 2]
    results = []
    for cell in args:
        grid, _, k = cell.partition('@')
        rows, cols = map(int, grid.split('x'))
        rec = (count_split(rows, cols, int(k), workers) if workers
               else count_cell(rows, cols, int(k)))
        rec.pop('all')
        print(json.dumps({x: rec[x] for x in rec if x != 'first_models'}), flush=True)
        results.append(rec)
        with open(out, 'w') as fh:
            json.dump(results, fh, indent=1)


if __name__ == '__main__':
    main()
