"""Six rows: SAT search for a valid blackout of w+8 points on the 6 x w grid.

Structure (proved in the paper, Lemma "one below the bound"): a valid blackout with w+8 points
has every column a singleton, a double, or empty; the double row pairs are distinct and form
one of
  K: K_{3,3} minus one edge, no empty column        (10 partitions x 9 edges = 90 cases)
  L: K_{2,4}, no empty column                        (15 cases)
  E: K_{3,3}, exactly one empty column               (10 cases)
Each double pair is used exactly once. Under this structure the incidence graph has no 4- or
6-cycle, so the axis-aligned rectangles are automatically identifiable, and only constraints
involving a tilted rectangle are needed, exactly as in six_row_structured_sat.py, whose
rectangle code and filters this script reuses.

Two encoders, one per run (both extend the ones in six_row_structured_sat.py):
  A: one "column type" variable per column and type (6 singletons, the doubles, and an empty
     type in case E); pairwise at-most-one; rectangles from verify_narrow; cadical153.
  B: edge-at-column variables, a "double" and an "empty" indicator per column; totalizer
     constraints; rectangles from a side-vector enumerator; glucose4.
Every model is rechecked by verify_narrow.collision and by the side-vector rectangle list, and
a valid witness gets the finite-collar test (7 boundary-row singletons per side).

Output: jis/data/six_row_excess8_w{width}_{encoder}.json.
Usage: python six_row_excess8_sat.py WIDTH A|B [CAP_SECONDS] [CASE_PREFIX]
CASE_PREFIX (K, L or E) restricts to one family.
"""
import json
import os
import sys
import time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)

import pysat
from pysat.card import CardEnc, EncType

from verify_narrow import axis_rectangles, collision, mask, rectangles
from six_row_structured_sat import (partitions, rectangles_by_sides, is_axis, tilted_clauses,
                                    collar_tests, solve_capped, one_based)

ROWS = 6


def cases():
    out = []
    for A, B in partitions():
        full = [(min(a, b), max(a, b)) for a in A for b in B]
        for miss in full:
            out.append(('K', [e for e in full if e != miss], False,
                        {'partition': [list(A), list(B)], 'missing_edge': list(miss)}))
    for small in combinations(range(ROWS), 2):
        big = [r for r in range(ROWS) if r not in small]
        edges = [(min(a, b), max(a, b)) for a in small for b in big]
        out.append(('L', edges, False, {'small_side': list(small)}))
    for A, B in partitions():
        edges = [(min(a, b), max(a, b)) for a in A for b in B]
        out.append(('E', edges, True, {'partition': [list(A), list(B)]}))
    return out


def _tilted_part(rects, flags, cols, edge_set, var, top, clauses, amo_enc):
    pair_clauses, full = tilted_clauses(rects, flags, cols, edge_set, var)
    clauses += pair_clauses
    f = []
    for corners in full:
        top += 1
        f.append(top)
        clauses.append([-v for v in corners] + [top])
    amo = CardEnc.atmost(lits=f, bound=1, top_id=top, encoding=amo_enc)
    clauses += amo.clauses
    return max(top, amo.nv), len(pair_clauses), len(f)


def encode_a(cols, edges, empty):
    edge_set = set(edges)
    var = {r * cols + x: r * cols + x + 1 for r in range(ROWS) for x in range(cols)}
    n = ROWS * cols
    types = [(r,) for r in range(ROWS)] + [tuple(e) for e in edges] + ([()] if empty else [])
    t = {(x, j): n + x * len(types) + j + 1 for x in range(cols) for j in range(len(types))}
    top = n + cols * len(types)
    clauses = []
    for x in range(cols):
        clauses.append([t[x, j] for j in range(len(types))])
        for j, k in combinations(range(len(types)), 2):
            clauses.append([-t[x, j], -t[x, k]])
        for r in range(ROWS):
            holders = [t[x, j] for j, ty in enumerate(types) if r in ty]
            for h in holders:
                clauses.append([-h, var[r * cols + x]])
            clauses.append([-var[r * cols + x]] + holders)
    for j in range(ROWS, len(types)):          # each double once, and the empty type once
        clauses.append([t[x, j] for x in range(cols)])
        for x, y in combinations(range(cols), 2):
            clauses.append([-t[x, j], -t[y, j]])
    rects = rectangles(ROWS, cols)
    axis = set(axis_rectangles(ROWS, cols))
    flags = [r not in axis for r in rects]
    top, npc, nf = _tilted_part(rects, flags, cols, edge_set, var, top, clauses,
                                EncType.seqcounter)
    return clauses, n, {'rectangles': len(rects), 'tilted': sum(flags), 'pair_clauses': npc,
                        'full_black_indicators': nf, 'variables': top, 'clauses': len(clauses)}


def encode_b(cols, edges, empty):
    edge_set = set(edges)
    var = {r * cols + x: r * cols + x + 1 for r in range(ROWS) for x in range(cols)}
    n = ROWS * cols
    q = len(edges)
    e = {(k, x): n + k * cols + x + 1 for k in range(q) for x in range(cols)}
    d = {x: n + q * cols + x + 1 for x in range(cols)}
    z = {x: n + (q + 1) * cols + x + 1 for x in range(cols)}
    top = n + (q + 2) * cols
    clauses = []
    for k, (a, b) in enumerate(edges):
        eq = CardEnc.equals(lits=[e[k, x] for x in range(cols)], bound=1, top_id=top,
                            encoding=EncType.totalizer)
        clauses += eq.clauses
        top = max(top, eq.nv)
        for x in range(cols):
            clauses.append([-e[k, x], var[a * cols + x]])
            clauses.append([-e[k, x], var[b * cols + x]])
            for r in range(ROWS):
                if r not in (a, b):
                    clauses.append([-e[k, x], -var[r * cols + x]])
    zc = CardEnc.equals(lits=[z[x] for x in range(cols)], bound=1 if empty else 0,
                        top_id=top, encoding=EncType.totalizer)
    clauses += zc.clauses
    top = max(top, zc.nv)
    for x in range(cols):
        for k, l in combinations(range(q), 2):
            clauses.append([-e[k, x], -e[l, x]])
        clauses.append([-d[x]] + [e[k, x] for k in range(q)])
        for k in range(q):
            clauses.append([-e[k, x], d[x]])
        clauses.append([-z[x], -d[x]])
        for r in range(ROWS):
            clauses.append([-z[x], -var[r * cols + x]])
        clauses.append([d[x], z[x]] + [var[r * cols + x] for r in range(ROWS)])
        for r, s in combinations(range(ROWS), 2):
            clauses.append([d[x], -var[r * cols + x], -var[s * cols + x]])
    rects = rectangles_by_sides(ROWS, cols)
    flags = [not is_axis(r, cols) for r in rects]
    top, npc, nf = _tilted_part(rects, flags, cols, edge_set, var, top, clauses,
                                EncType.totalizer)
    return clauses, n, {'rectangles': len(rects), 'tilted': sum(flags), 'pair_clauses': npc,
                        'full_black_indicators': nf, 'variables': top, 'clauses': len(clauses)}


def main():
    cols = int(sys.argv[1])
    enc = sys.argv[2].upper()
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 1800
    only = sys.argv[4].upper() if len(sys.argv) > 4 else None
    encoder, solver = (encode_a, 'cadical153') if enc == 'A' else (encode_b, 'glucose4')
    full_rects = rectangles(ROWS, cols)
    side_rects = rectangles_by_sides(ROWS, cols)
    suffix = '' if only is None else f'_{only}'
    path = os.path.join(ROOT, 'jis', 'data', f'six_row_excess8_w{cols}_{enc}{suffix}.json')
    results = []
    for family, edges, empty, label in cases():
        if only and family != only:
            continue
        t0 = time.time()
        clauses, n, info = encoder(cols, edges, empty)
        gen = time.time() - t0
        status, model, dt = solve_capped(solver, clauses, cap)
        rec = {'rows': ROWS, 'width': cols, 'target': cols + 8, 'family': family,
               'case': label, 'zero_based_edges': [list(e) for e in edges],
               'encoder': enc, 'solver': solver, 'pysat_version': pysat.__version__,
               'status': status, 'encode_seconds': round(gen, 1),
               'solve_seconds': round(dt, 1), 'cap_seconds': cap, **info}
        if model is not None:
            pts = {((v - 1) % cols, (v - 1) // cols) for v in model if 0 < v <= n}
            black = mask(pts, cols)
            rec['witness'] = one_based(pts)
            rec['witness_size'] = len(pts)
            rec['witness_valid_by_verify_narrow'] = collision(full_rects, black) is None
            rec['witness_valid_by_side_vectors'] = collision(side_rects, black) is None
            rec['picture'] = [''.join('#' if (x, y) in pts else '.' for x in range(cols))
                              for y in range(ROWS)]
            if rec['witness_valid_by_verify_narrow']:
                rec['collar'] = collar_tests(pts, cols)
        print(json.dumps({k: v for k, v in rec.items()
                          if k not in ('witness', 'collar', 'zero_based_edges')}), flush=True)
        results.append(rec)
        with open(path, 'w') as fh:
            json.dump(results, fh, indent=1)


if __name__ == '__main__':
    main()
