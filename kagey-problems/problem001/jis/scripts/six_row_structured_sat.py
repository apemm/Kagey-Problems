"""Six rows: SAT search for a blackout of w+9 points on the 6 x w grid.

Such a blackout has the equality structure of the row bound: nine columns black in exactly
two rows, their row pairs the nine edges of K_{3,3} for one partition of the rows into two
triples, each edge used once, and every other column black in exactly one row. Under this
structure the axis-aligned rectangles are automatically identifiable (no 4- or 6-cycle in
the incidence graph), so the instance only needs the constraints that involve a tilted
rectangle: for every pair of rectangles sharing a corner with at least one tilted, not all
of their symmetric difference is black; and at most one tilted rectangle is fully black
(pairs with disjoint corner sets collide exactly when both are fully black). Clauses that
the column structure already makes true (a column with three points of the difference, or
two points whose rows are not an edge of the partition, or two columns carrying the same
edge) are dropped.

Two encoders written separately, one per run:
  A: rectangles from verify_narrow.rectangles and verify_narrow.axis_rectangles; one
     "column type" variable per column and type (6 singleton types, 9 double types);
     pairwise at-most-one constraints; solver cadical153.
  B: rectangles from a side-vector enumerator; edge-at-column variables plus a "column is
     a double" variable; totalizer and sequential-counter constraints; solver glucose4.
Every model is rechecked by verify_narrow.collision on the full rectangle list, and a valid
witness is put through the finite-collar test (7 boundary-row singleton columns on the
left, on the right, and on both sides, for row 1 and for row 6), with both enumerators.

Output: jis/data/six_row_sat_w{width}_{encoder}.json. One-based (column, row) in the
output; zero-based inside. Usage: python six_row_structured_sat.py WIDTH A|B [CAP_SECONDS]
"""
import json
import os
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

from verify_narrow import axis_rectangles, collision, mask, rectangles

ROWS = 6                                    # --rows 5 reruns the five-row calibration
COLLAR = 1 + (ROWS - 1) ** 2 // 4


def bits(x):
    return [i for i in range(x.bit_length()) if x >> i & 1]


def partitions():
    """Row partitions into parts of sizes floor(h/2) and ceil(h/2); each once."""
    out = []
    seen = set()
    for a in combinations(range(ROWS), ROWS // 2):
        b = tuple(r for r in range(ROWS) if r not in a)
        key = frozenset((a, b))
        if key not in seen:
            seen.add(key)
            out.append((a, b))
    return out


def rectangles_by_sides(rows, cols):
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
                found.add(mask(((x, y), (x + a, y + b), (x + c, y + d),
                                (x + a + c, y + b + d)), cols))
    return sorted(found)


def is_axis(r, cols):
    xs = {i % cols for i in bits(r)}
    ys = {i // cols for i in bits(r)}
    return len(xs) == 2 and len(ys) == 2


def feasible(d, cols, edge_set):
    """Can the point set d be entirely black under the equality structure?"""
    cols_rows = {}
    for i in bits(d):
        cols_rows.setdefault(i % cols, []).append(i // cols)
    used = set()
    for x, rs in cols_rows.items():
        if len(rs) >= 3:
            return False
        if len(rs) == 2:
            e = (min(rs), max(rs))
            if e not in edge_set or e in used:
                return False
            used.add(e)
    return True


def tilted_clauses(rects, tilted_flags, cols, edge_set, var):
    """Clauses (as lists of negative point literals) for pairs sharing a corner with at
    least one tilted member, filtered by feasibility; plus the corner lists of the
    feasible tilted rectangles for the indicator constraints."""
    by_corner = {}
    for idx, r in enumerate(rects):
        for i in bits(r):
            by_corner.setdefault(i, []).append(idx)
    clauses = []
    seen = set()
    for i, lst in by_corner.items():
        for a, b in combinations(lst, 2):
            if not (tilted_flags[a] or tilted_flags[b]):
                continue
            if (a, b) in seen:
                continue
            seen.add((a, b))
            d = rects[a] ^ rects[b]
            if feasible(d, cols, edge_set):
                clauses.append([-var[i] for i in bits(d)])
    full = [[var[i] for i in bits(r)] for r, t in zip(rects, tilted_flags)
            if t and feasible(r, cols, edge_set)]
    return clauses, full


# ---------------------------------------------------------------- encoder A

def encode_a(cols, part):
    A, B = part
    edges = [(min(a, b), max(a, b)) for a in A for b in B]
    edge_set = set(edges)
    var = {r * cols + x: r * cols + x + 1 for r in range(ROWS) for x in range(cols)}
    n = ROWS * cols
    types = [(r,) for r in range(ROWS)] + [tuple(e) for e in edges]       # 15 types
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
    for j in range(ROWS, len(types)):                                       # each edge once
        clauses.append([t[x, j] for x in range(cols)])
        for x, y in combinations(range(cols), 2):
            clauses.append([-t[x, j], -t[y, j]])
    rects = rectangles(ROWS, cols)
    axis = set(axis_rectangles(ROWS, cols))
    flags = [r not in axis for r in rects]
    pair_clauses, full = tilted_clauses(rects, flags, cols, edge_set, var)
    clauses += pair_clauses
    f = []
    for corners in full:
        top += 1
        f.append(top)
        clauses.append([-v for v in corners] + [top])
    amo = CardEnc.atmost(lits=f, bound=1, top_id=top, encoding=EncType.seqcounter)
    clauses += amo.clauses
    top = max(top, amo.nv)
    info = {'rectangles': len(rects), 'tilted': sum(flags), 'pair_clauses': len(pair_clauses),
            'full_black_indicators': len(f), 'variables': top, 'clauses': len(clauses)}
    return clauses, n, info, rects


# ---------------------------------------------------------------- encoder B

def encode_b(cols, part):
    A, B = part
    edges = [(min(a, b), max(a, b)) for a in A for b in B]
    edge_set = set(edges)
    var = {r * cols + x: r * cols + x + 1 for r in range(ROWS) for x in range(cols)}
    n = ROWS * cols
    q = len(edges)
    e = {(k, x): n + k * cols + x + 1 for k in range(q) for x in range(cols)}
    d = {x: n + q * cols + x + 1 for x in range(cols)}
    top = n + (q + 1) * cols
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
    for x in range(cols):
        for k, l in combinations(range(q), 2):
            clauses.append([-e[k, x], -e[l, x]])
        clauses.append([-d[x]] + [e[k, x] for k in range(q)])
        for k in range(q):
            clauses.append([-e[k, x], d[x]])
        clauses.append([d[x]] + [var[r * cols + x] for r in range(ROWS)])
        for r, s in combinations(range(ROWS), 2):
            clauses.append([d[x], -var[r * cols + x], -var[s * cols + x]])
    rects = rectangles_by_sides(ROWS, cols)
    flags = [not is_axis(r, cols) for r in rects]
    pair_clauses, full = tilted_clauses(rects, flags, cols, edge_set, var)
    clauses += pair_clauses
    f = []
    for corners in full:
        top += 1
        f.append(top)
        clauses.append([-v for v in corners] + [top])
    amo = CardEnc.atmost(lits=f, bound=1, top_id=top, encoding=EncType.totalizer)
    clauses += amo.clauses
    top = max(top, amo.nv)
    info = {'rectangles': len(rects), 'tilted': sum(flags), 'pair_clauses': len(pair_clauses),
            'full_black_indicators': len(f), 'variables': top, 'clauses': len(clauses)}
    return clauses, n, info, rects


# ---------------------------------------------------------------- checks

def one_based(pts):
    return sorted((x + 1, y + 1) for x, y in pts)


def collar_tests(pts, cols):
    out = {}
    for row in (0, ROWS - 1):
        for side in ('left', 'right', 'both'):
            left = COLLAR if side in ('left', 'both') else 0
            right = COLLAR if side in ('right', 'both') else 0
            w = cols + left + right
            shifted = {(x + left, y) for x, y in pts}
            shifted |= {(x, row) for x in range(left)}
            shifted |= {(cols + left + x, row) for x in range(right)}
            black = mask(shifted, w)
            r1 = rectangles(ROWS, w)
            r2 = rectangles_by_sides(ROWS, w)
            out[f'row{row + 1}_{side}'] = {
                'width': w, 'rectangles': len(r1), 'enumerators_agree': sorted(r1) == r2,
                'valid_by_verify_narrow': collision(r1, black) is None,
                'valid_by_side_vectors': collision(r2, black) is None,
                'points': one_based(shifted)}
    return out


def solve_capped(name, clauses, cap):
    t0 = time.time()
    with Solver(name=name, bootstrap_with=clauses) as s:
        timer = threading.Timer(cap, s.interrupt)
        timer.start()
        try:
            r = s.solve_limited(expect_interrupt=True)
        finally:
            timer.cancel()
        model = s.get_model() if r else None
    return ('SAT' if r else 'UNSAT' if r is False else 'unresolved'), model, time.time() - t0


def main():
    global ROWS, COLLAR
    args = sys.argv[1:]
    if args[:1] == ['--rows']:
        ROWS = int(args[1])
        COLLAR = 1 + (ROWS - 1) ** 2 // 4
        args = args[2:]
    cols = int(args[0])
    enc = args[1].upper()
    cap = int(args[2]) if len(args) > 2 else 1800
    q = (ROWS * ROWS) // 4
    encoder, solver = (encode_a, 'cadical153') if enc == 'A' else (encode_b, 'glucose4')
    results = []
    full_rects = rectangles(ROWS, cols)
    for part in partitions():
        t0 = time.time()
        clauses, n, info, _ = encoder(cols, part)
        gen = time.time() - t0
        status, model, dt = solve_capped(solver, clauses, cap)
        rec = {'rows': ROWS, 'width': cols, 'target': cols + q, 'encoder': enc,
               'solver': solver, 'pysat_version': pysat.__version__,
               'partition_zero_based_rows': [list(part[0]), list(part[1])],
               'status': status, 'encode_seconds': round(gen, 1),
               'solve_seconds': round(dt, 1), 'cap_seconds': cap, **info}
        if model is not None:
            pts = {((v - 1) % cols, (v - 1) // cols) for v in model if 0 < v <= n}
            black = mask(pts, cols)
            rec['witness'] = one_based(pts)
            rec['witness_size'] = len(pts)
            rec['witness_valid_by_verify_narrow'] = collision(full_rects, black) is None
            rec['witness_valid_by_side_vectors'] = collision(
                rectangles_by_sides(ROWS, cols), black) is None
            rec['picture'] = [''.join('#' if (x, y) in pts else '.' for x in range(cols))
                              for y in range(ROWS)]
            if rec['witness_valid_by_verify_narrow']:
                rec['collar'] = collar_tests(pts, cols)
        print(json.dumps({k: v for k, v in rec.items() if k not in ('witness', 'collar')}),
              flush=True)
        if 'collar' in rec:
            print('  collar:', {k: (v['valid_by_verify_narrow'], v['valid_by_side_vectors'])
                                for k, v in rec['collar'].items()}, flush=True)
        results.append(rec)
        tag = '' if ROWS == 6 else f'_rows{ROWS}'
        path = os.path.join(ROOT, 'jis', 'data', f'six_row_sat{tag}_w{cols}_{enc}.json')
        with open(path, 'w') as fh:
            json.dump(results, fh, indent=1)


if __name__ == '__main__':
    main()
