"""Second SAT encoding of "the 5 x m grid has a valid blackout of k points".

Point variables only: x_p is true when the point p is blacked out.  For every
pair of distinct rectangles with corner sets C1, C2 the clause says that the
symmetric difference C1 ^ C2 is not entirely black (Lemma 1 of PROBLEM.md:
the two presentations coincide exactly when the difference is black).
Differences that contain a smaller difference are dropped (sizes are 2, 4, 6
or 8, so the subset test is a submask enumeration).  "At least k black" is a
totalizer from pysat.card.  With --colmax2 every column gets "at least one,
at most two black points" and the differences with three points in one column
are dropped as implied; this is only used to find witnesses at large widths.

Rectangles come from five_row_geometry_check (corner plus two perpendicular
side vectors).  Each instance runs in its own process under a wall-clock cap
and is recorded as "unresolved" if the cap is hit.  The witness of a
satisfiable instance is rechecked by the presentation test and reported in
one-based (column, row) coordinates.

Usage:  five_row_sat_check.py --run WIDTH BOUND [--colmax2] [--solver NAME]
        five_row_sat_check.py            (the schedule in main)
"""
import json
import os
import subprocess
import sys
import time
from itertools import combinations

from five_row_geometry_check import (rectangles_by_sides, presentation_collision,
                                     one_based_from_mask, picture)

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, '..', 'data')
ROWS = 5


def minimal_differences(rects, cols, colmax2):
    diffs = set()
    for a, b in combinations(rects, 2):
        diffs.add(a ^ b)
    distinct = len(diffs)
    dropped_col = 0
    if colmax2:
        full = (1 << cols) - 1
        kept = set()
        for d in diffs:
            r = [(d >> (i * cols)) & full for i in range(ROWS)]
            triple = 0
            for i, j, k in combinations(range(ROWS), 3):
                triple |= r[i] & r[j] & r[k]
            if triple:
                dropped_col += 1
            else:
                kept.add(d)
        diffs = kept
    by_size = {}
    for d in diffs:
        by_size.setdefault(d.bit_count(), []).append(d)
    sizes = sorted(by_size)
    minimal = set()
    pruned = 0
    if len(diffs) <= 600000:
        for s in sizes:
            for d in by_size[s]:
                bits = [1 << i for i in range(d.bit_length()) if d >> i & 1]
                contained = False
                for t in sizes:
                    if t >= s:
                        break
                    for sub in combinations(bits, t):
                        if sum(sub) in minimal:
                            contained = True
                            break
                    if contained:
                        break
                if contained:
                    pruned += 1
                else:
                    minimal.add(d)
    else:
        minimal = diffs
    return sorted(minimal), distinct, dropped_col, pruned


def run_instance(cols, bound, colmax2, solver_name):
    from pysat.card import CardEnc, EncType
    from pysat.formula import CNF
    from pysat.solvers import Solver
    t0 = time.time()
    rects = rectangles_by_sides(ROWS, cols)
    diffs, distinct, dropped_col, pruned = minimal_differences(rects, cols, colmax2)

    def var(x, y):
        return 1 + y * cols + x

    cnf = CNF()
    for d in diffs:
        cnf.append([-(i + 1) for i in range(d.bit_length()) if d >> i & 1])
    difference_clauses = len(cnf.clauses)
    structural = 0
    if colmax2:
        for x in range(cols):
            lits = [var(x, y) for y in range(ROWS)]
            cnf.append(lits)
            for trip in combinations(lits, 3):
                cnf.append([-l for l in trip])
            structural += 11
    top = ROWS * cols
    card = CardEnc.atleast(lits=list(range(1, top + 1)), bound=bound, top_id=top,
                           encoding=EncType.totalizer)
    cnf.extend(card.clauses)
    build = time.time() - t0
    t1 = time.time()
    with Solver(name=solver_name, bootstrap_with=cnf.clauses) as s:
        sat = s.solve()
        model = s.get_model() if sat else None
    solve = time.time() - t1
    rec = {'width': cols, 'bound': bound, 'colmax2': colmax2, 'solver': solver_name,
           'status': 'SAT' if sat else 'UNSAT', 'rectangles': len(rects),
           'distinct_differences': distinct, 'dropped_three_in_a_column': dropped_col,
           'dropped_supersets': pruned, 'difference_clauses': difference_clauses,
           'structural_clauses': structural, 'cardinality_clauses': len(card.clauses),
           'clauses': len(cnf.clauses), 'variables': max(top, card.nv),
           'build_seconds': round(build, 2), 'solve_seconds': round(solve, 2)}
    if sat:
        black = 0
        for lit in model:
            if 0 < lit <= top:
                black |= 1 << (lit - 1)
        rec['witness_size'] = black.bit_count()
        rec['witness_one_based'] = one_based_from_mask(black, ROWS, cols)
        rec['witness_picture'] = picture(black, ROWS, cols)
        rec['witness_valid_by_presentation_test'] = presentation_collision(rects, black) is None
    return rec


def launch(cols, bound, colmax2, solver_name, cap):
    args = [sys.executable, os.path.abspath(__file__), '--run', str(cols), str(bound), '--solver', solver_name]
    if colmax2:
        args.append('--colmax2')
    t0 = time.time()
    try:
        p = subprocess.run(args, capture_output=True, text=True, timeout=cap, cwd=HERE)
        wall = time.time() - t0
        if p.returncode != 0:
            return {'width': cols, 'bound': bound, 'colmax2': colmax2, 'solver': solver_name,
                    'status': 'error', 'stderr': p.stderr[-2000:], 'wall_seconds': round(wall, 1)}
        rec = json.loads(p.stdout.strip().splitlines()[-1])
    except subprocess.TimeoutExpired:
        return {'width': cols, 'bound': bound, 'colmax2': colmax2, 'solver': solver_name,
                'status': 'unresolved', 'cap_seconds': cap, 'wall_seconds': round(time.time() - t0, 1)}
    rec['wall_seconds'] = round(wall, 1)
    return rec


def main():
    if '--run' in sys.argv:
        i = sys.argv.index('--run')
        cols, bound = int(sys.argv[i + 1]), int(sys.argv[i + 2])
        solver_name = sys.argv[sys.argv.index('--solver') + 1] if '--solver' in sys.argv else 'glucose3'
        print(json.dumps(run_instance(cols, bound, '--colmax2' in sys.argv, solver_name)))
        return
    import pysat
    schedule = []
    for m in (5, 6, 7):
        schedule.append((m, m + 5, False, 'glucose3', 1200))
        schedule.append((m, m + 6, False, 'glucose3', 1200))
    for m in range(8, 13):
        schedule.append((m, m + 6, False, 'glucose3', 1200))
    schedule.append((8, 15, False, 'glucose3', 1200))
    schedule.append((9, 16, False, 'glucose3', 1200))
    for m in range(13, 21):
        schedule.append((m, m + 6, True, 'glucose3', 900))
    for m, k in ((5, 11), (6, 12), (7, 13), (8, 15), (9, 16)):
        schedule.append((m, k, False, 'lingeling', 1200))
    out = {'method': 'point-variable SAT, minimal rectangle differences, totalizer cardinality',
           'solvers': 'glucose3 and lingeling (pysat names)', 'pysat_version': pysat.__version__,
           'python_version': sys.version.split()[0], 'coordinates': 'one-based (column,row)',
           'instances': []}
    path = os.path.join(DATA, 'five_row_sat_check.json')
    for cols, bound, colmax2, solver_name, cap in schedule:
        rec = launch(cols, bound, colmax2, solver_name, cap)
        out['instances'].append(rec)
        print(json.dumps({k: v for k, v in rec.items() if k not in ('witness_one_based', 'witness_picture')}),
              flush=True)
        with open(path, 'w') as f:
            json.dump(out, f, indent=1)


if __name__ == '__main__':
    main()
