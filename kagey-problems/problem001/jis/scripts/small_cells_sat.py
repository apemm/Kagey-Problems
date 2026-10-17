"""Exact maximum blackout on the 6 x 7, 6 x 8 and 7 x 7 grids by SAT.

Lower bound: the staircase-plus-one blackouts stored in game/game.js (h+m points) are read
and rechecked with verify_narrow.collision. Upper bound: "there is a valid blackout of
h+m+1 points" is encoded twice, from scratch each time, and both instances are reported
(UNSAT for both proves the value h+m).

Encoding A: rectangles from verify_narrow.rectangles (equal diagonals with a common
midpoint); one clause per minimal pairwise symmetric difference D ("not all of D black");
|S| >= k by a sequential counter (pysat.card, seqcounter); solver cadical153.

Encoding B: rectangles enumerated from a corner and two perpendicular side vectors (no
shared code with verify_narrow); one clause per pair of rectangles that share a corner
("not all of the symmetric difference black"); pairs with disjoint corner sets are covered
by one indicator per rectangle ("all four corners black") and an at-most-one constraint;
|S| >= k by a totalizer; solver glucose4, repeated with minisat22.

Every satisfying model is turned into a blackout and rechecked by verify_narrow.collision.
Output: jis/data/small_cells_sat.json. Coordinates in the output are one-based (column,
row) with (1,1) top-left, as in verify_narrow.py; internally the grid is zero-based.
Usage: python small_cells_sat.py [cells ...]   e.g. 6x7 6x8 7x7   (default: all three);
a cell may carry explicit bounds, e.g. 6x8@16,17 (default: h+m and h+m+1).
"""
import json
import os
import re
import sys
import threading
import time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, ROOT)

import pysat
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

from verify_narrow import collision, mask, rectangles

CAP_SECONDS = 1800


# ---------------------------------------------------------------- helpers

def bits(x):
    return [i for i in range(x.bit_length()) if x >> i & 1]


def points_one_based(black, cols):
    """Zero-based bitmask (bit y*cols+x) -> sorted list of one-based (column, row)."""
    return sorted((i % cols + 1, i // cols + 1) for i in bits(black))


def solve_capped(name, clauses, cap=CAP_SECONDS):
    """Run a pysat solver with a wall-clock cap. Returns (status, model, seconds)."""
    t0 = time.time()
    with Solver(name=name, bootstrap_with=clauses) as s:
        timer = threading.Timer(cap, s.interrupt)
        timer.start()
        try:
            r = s.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
        model = s.get_model() if r else None
    dt = time.time() - t0
    status = 'SAT' if r else ('UNSAT' if r is False else 'unresolved')
    return status, model, dt


def game_witness(rows, cols):
    path = os.path.join(ROOT, 'game', 'game.js')
    src = open(path).read()
    start = src.index('var WITNESS = {')
    block = src[start:src.index('};', start)]
    for key, body in re.findall(r"'(\d+x\d+)': \[([^\]]*)\]", block):
        if key == f'{rows}x{cols}':
            picture = re.findall(r"'([.#]+)'", body)
            return mask([(x, y) for y in range(rows) for x in range(cols)
                         if picture[y][x] == '#'], cols)
    return None


# ---------------------------------------------------------------- encoding A

def minimal_differences(rects):
    """All pairwise symmetric differences, keeping only the inclusion-minimal ones."""
    diffs = {a ^ b for a, b in combinations(rects, 2)}
    by_size = sorted(diffs, key=lambda d: d.bit_count())
    kept = []
    for d in by_size:
        if not any(k & d == k for k in kept if k != d):
            kept.append(d)
    return kept, len(diffs)


def encoding_a(rows, cols, k):
    rects = rectangles(rows, cols)
    n = rows * cols
    kept, npairs = minimal_differences(rects)
    clauses = [[-(i + 1) for i in bits(d)] for d in kept]
    card = CardEnc.atleast(lits=list(range(1, n + 1)), bound=k, top_id=n,
                           encoding=EncType.seqcounter)
    all_clauses = clauses + card.clauses
    nvars = max(n, card.nv)
    info = {'rectangles': len(rects), 'distinct_differences': npairs,
            'minimal_differences': len(kept), 'variables': nvars,
            'clauses': len(all_clauses), 'cardinality': 'seqcounter'}
    return all_clauses, n, info


# ---------------------------------------------------------------- encoding B

def rectangles_by_sides(rows, cols):
    """Rectangles as frozensets of zero-based (x, y) corners: a corner P and two
    perpendicular nonzero side vectors u, v with P, P+u, P+v, P+u+v on the grid."""
    pts = [(x, y) for y in range(rows) for x in range(cols)]
    inside = set(pts)
    vectors = [(a, b) for a in range(-(cols - 1), cols) for b in range(-(rows - 1), rows)
               if (a, b) != (0, 0)]
    found = set()
    for (x, y) in pts:
        for (a, b) in vectors:
            if (x + a, y + b) not in inside:
                continue
            for (c, d) in vectors:
                if a * c + b * d != 0:
                    continue
                if (x + c, y + d) not in inside or (x + a + c, y + b + d) not in inside:
                    continue
                found.add(frozenset(((x, y), (x + a, y + b), (x + c, y + d),
                                     (x + a + c, y + b + d))))
    return sorted(found, key=sorted)


def encoding_b(rows, cols, k):
    rects = rectangles_by_sides(rows, cols)
    n = rows * cols
    var = {(x, y): y * cols + x + 1 for y in range(rows) for x in range(cols)}
    by_corner = {}
    for idx, r in enumerate(rects):
        for p in r:
            by_corner.setdefault(p, []).append(idx)
    clauses = []
    seen = set()
    for p, lst in by_corner.items():
        for i, j in combinations(lst, 2):
            if (i, j) in seen:
                continue
            seen.add((i, j))
            diff = rects[i] ^ rects[j]
            clauses.append([-var[q] for q in diff])
    sharing = len(clauses)
    # indicator f_r: all four corners black -> f_r; at most one f_r
    top = n
    f = []
    for r in rects:
        top += 1
        f.append(top)
        clauses.append([-var[q] for q in r] + [top])
    amo = CardEnc.atmost(lits=f, bound=1, top_id=top, encoding=EncType.seqcounter)
    clauses += amo.clauses
    top = max(top, amo.nv)
    card = CardEnc.atleast(lits=list(range(1, n + 1)), bound=k, top_id=top,
                           encoding=EncType.totalizer)
    clauses += card.clauses
    top = max(top, card.nv)
    info = {'rectangles': len(rects), 'pairs_sharing_a_corner': sharing,
            'variables': top, 'clauses': len(clauses),
            'at_most_one_full': 'seqcounter', 'cardinality': 'totalizer'}
    return clauses, n, info


# ---------------------------------------------------------------- driver

def model_to_mask(model, n):
    return sum(1 << (v - 1) for v in model if 0 < v <= n)


def run_cell(rows, cols, bounds=None):
    out = {'grid': f'{rows}x{cols}', 'rows': rows, 'cols': cols,
           'coordinates': 'one-based (column,row), (1,1) top-left', 'runs': []}
    rects_vn = rectangles(rows, cols)
    out['rectangles_verify_narrow'] = len(rects_vn)
    out['rectangles_by_sides'] = len(rectangles_by_sides(rows, cols))
    g = game_witness(rows, cols)
    out['game_witness'] = None
    if g is not None:
        out['game_witness'] = {'points': points_one_based(g, cols), 'size': g.bit_count(),
                               'valid_by_verify_narrow': collision(rects_vn, g) is None}
    lower = rows + cols
    for k in bounds or (lower, lower + 1):
        for enc_name, enc, solvers in (('A', encoding_a, ['cadical153']),
                                       ('B', encoding_b, ['glucose4', 'minisat22'])):
            t0 = time.time()
            clauses, n, info = enc(rows, cols, k)
            gen = time.time() - t0
            for sname in solvers:
                status, model, dt = solve_capped(sname, clauses)
                rec = {'bound': k, 'encoding': enc_name, 'solver': sname,
                       'pysat_version': pysat.__version__, 'status': status,
                       'encode_seconds': round(gen, 2), 'solve_seconds': round(dt, 2),
                       **info}
                if model is not None:
                    black = model_to_mask(model, n)
                    rec['witness'] = points_one_based(black, cols)
                    rec['witness_size'] = black.bit_count()
                    rec['witness_valid_by_verify_narrow'] = collision(rects_vn, black) is None
                out['runs'].append(rec)
                print(json.dumps(rec), flush=True)
    return out


def main():
    cells = sys.argv[1:] or ['6x7', '6x8', '7x7']
    results = []
    for cell in cells:
        grid, _, bounds = cell.partition('@')          # e.g. 6x8@16,17
        rows, cols = map(int, grid.split('x'))
        bounds = [int(b) for b in bounds.split(',')] if bounds else None
        results.append(run_cell(rows, cols, bounds))
        path = os.path.join(ROOT, 'jis', 'data', f'small_cells_sat_{cell.replace("@", "_b")}.json')
        with open(path, 'w') as fh:
            json.dump(results[-1], fh, indent=1)
    path = os.path.join(ROOT, 'jis', 'data', 'small_cells_sat.json')
    if len(cells) == 3:
        with open(path, 'w') as fh:
            json.dump(results, fh, indent=1)


if __name__ == '__main__':
    main()
