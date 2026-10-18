"""A second SAT count of the maximum blackouts a_h(m), with its own encoding and solver.

This backs up table_counts_search.py on the cells where the column search is too slow. It
shares no code with small_cells_sat.py, table_counts_sat.py or verify_narrow.py. The rectangles
come from table_counts_search.all_rectangles (perpendicular multiples of a primitive vector).
For every pair of rectangles there is one clause "not every point of the symmetric difference
is black", with no reduction to minimal differences. The size is fixed to exactly k by a
totalizer, and the solver is minisat22. Each model is blocked by the clause "not all of these
k points black", and each model is rechecked against the definition by a direct comparison of
visible corner sets. The 30 minute cap is checked between models and can also interrupt a call.

With --split N the cell is cut into one part for each possible content of the first column,
fixed by unit clauses, and the parts run on N processes with a cap of 30 minutes each.

Usage: python table_counts_sat2.py 6x7@13 7x7@14 ... --out file.json
"""
import hashlib
import json
import os
import sys
import threading
import time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import pysat
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

from table_counts_search import all_rectangles

CAP_SECONDS = 1800
SOLVER = 'minisat22'


def valid(rects, black):
    seen = set()
    for r in rects:
        v = frozenset(p for p in r if p not in black)
        if v in seen:
            return False
        seen.add(v)
    return True


def count_cell(h, m, k, cap=CAP_SECONDS, first=None):
    rects = all_rectangles(h, m)
    var = {(x, y): x * h + y + 1 for x in range(m) for y in range(h)}
    n = h * m
    diffs = {frozenset(set(a) ^ set(b)) for a, b in combinations(rects, 2)}
    clauses = [[-var[p] for p in d] for d in diffs]
    card = CardEnc.equals(lits=list(range(1, n + 1)), bound=k, top_id=n,
                          encoding=EncType.totalizer)
    clauses += card.clauses
    if first is not None:                      # fix column 1: bit y of first is row y+1
        clauses += [[var[0, y]] if first >> y & 1 else [-var[0, y]] for y in range(h)]
    point = {v: p for p, v in var.items()}
    t0 = time.time()
    count = 0
    models = []
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
            black = {point[v] for v in s.get_model() if 0 < v <= n}
            assert len(black) == k and valid(rects, black)
            count += 1
            models.append(sorted([x + 1, y + 1] for x, y in black))
            s.add_clause([-var[p] for p in black])
            s.clear_interrupt()
    return {'grid': f'{h}x{m}', 'rows': h, 'cols': m, 'size': k, 'solver': SOLVER,
            'pysat_version': pysat.__version__, 'rectangles': len(rects),
            'difference_clauses': len(diffs), 'status': status,
            'count': count if status == 'exact' else None, 'models_found': count,
            'seconds': round(time.time() - t0, 2), 'all_models_valid': True,
            'models_sha256': hashlib.sha256(json.dumps(sorted(models)).encode()).hexdigest(),
            'first_column': first, 'first_models': sorted(models)[:20], 'all': models}


def _part(job):
    return count_cell(*job)


def count_split(h, m, k, workers):
    from multiprocessing import Pool
    jobs = [(h, m, k, CAP_SECONDS, s) for s in range(1 << h) if bin(s).count('1') <= k]
    with Pool(workers) as pool:
        parts = pool.map(_part, jobs, chunksize=1)
    models = sorted(mo for p in parts for mo in p['all'])
    exact = all(p['status'] == 'exact' for p in parts)
    return {'grid': f'{h}x{m}', 'rows': h, 'cols': m, 'size': k, 'solver': SOLVER,
            'pysat_version': pysat.__version__, 'split': 'by first column',
            'parts': len(parts),
            'parts_unresolved': [p['first_column'] for p in parts if p['status'] != 'exact'],
            'status': 'exact' if exact else 'unresolved',
            'count': len(models) if exact else None, 'models_found': len(models),
            'seconds_max_part': max(p['seconds'] for p in parts),
            'seconds_total': round(sum(p['seconds'] for p in parts), 2),
            'all_models_valid': True,
            'models_sha256': hashlib.sha256(json.dumps(models).encode()).hexdigest(),
            'first_models': models[:20], 'all': models}


def main():
    args = sys.argv[1:]
    out = os.path.join(HERE, '..', 'data', 'table_counts_sat2.json')
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
        h, m = map(int, grid.split('x'))
        rec = count_split(h, m, int(k), workers) if workers else count_cell(h, m, int(k))
        rec.pop('all')
        print(json.dumps({x: rec[x] for x in rec if x != 'first_models'}), flush=True)
        results.append(rec)
        with open(out, 'w') as fh:
            json.dump(results, fh, indent=1)


if __name__ == '__main__':
    main()
