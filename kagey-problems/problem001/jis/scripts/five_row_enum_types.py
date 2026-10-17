"""Enumerate the blackouts of m+6 points of the 5 x m grid by SAT with blocking clauses,
column-type encoding, without assuming the bipartite structure of the row pairs.

Variables: one per column and column type, 15 types (5 singleton rows, 10 row pairs). Exactly
one type per column (one clause plus pairwise exclusions) and exactly six pair-typed columns
(pysat.card sequential counter, both directions). A column with three or more black points
never occurs in a blackout of m+6 points on five rows (row bound proof), so this hypothesis is
weaker than the equality structure: the complete bipartite shape of the six pairs is not
imposed and has to come out of the clauses.

Rectangles come from five_row_sidevec.rectangles_sidevec (corner plus perpendicular side
vectors) and are compared with verify_narrow.rectangles. For every pair of distinct rectangles
with corner symmetric difference D, the clause "some point of D is white": for a column x
holding one point (x,y) of D the literals are the types of x that avoid y; for two points
(x,r),(x,s) the literals are the 14 types other than the pair {r,s}; a column with three points
of D makes the clause true. Differences that contain a smaller difference are dropped.

Restrictions (the sub-families compared with the other encoding): --singleton-rows lists the
one-based rows allowed for singleton columns; --double-columns lists the one-based columns
that must be the pair-typed ones.

Each model is rechecked with verify_narrow.collision and blocked by negating its column types.
The run stops at the cap or at the wall-clock limit and says so.

Usage: python five_row_enum_types.py WIDTH [--solver glucose4] [--cap 10000] [--minutes 30]
          [--singleton-rows 1] [--double-columns 1,5,9,13,17,21] [--out FILE] [--tag NAME]
Output JSON: ONE-BASED (column, row) points, (1,1) top-left.
"""
import argparse
import json
import os
import sys
import threading
import time
from itertools import combinations

import pysat
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, ROOT)
import verify_narrow  # noqa: E402
from five_row_sidevec import rectangles_sidevec  # noqa: E402

DATA_DIR = os.path.join(HERE, '..', 'data')
ROWS = 5
TYPES = [(r,) for r in range(ROWS)] + list(combinations(range(ROWS), 2))   # 15


def minimal_differences(rects):
    diffs = {a ^ b for a, b in combinations(rects, 2)}
    by_size = sorted(diffs, key=lambda d: bin(d).count('1'))
    kept = []
    keptset = set()
    for d in by_size:
        # d is redundant if some kept difference is a proper subset of d
        bits = [1 << i for i in range(d.bit_length()) if d >> i & 1]
        redundant = False
        for n in range(1, len(bits)):
            for sub in combinations(bits, n):
                if sum(sub) in keptset:
                    redundant = True
                    break
            if redundant:
                break
        if not redundant:
            kept.append(d)
            keptset.add(d)
    return len(diffs), kept


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('width', type=int)
    ap.add_argument('--solver', default='glucose4')
    ap.add_argument('--cap', type=int, default=10000)
    ap.add_argument('--minutes', type=float, default=30.0)
    ap.add_argument('--singleton-rows', default=None)
    ap.add_argument('--double-columns', default=None)
    ap.add_argument('--out', default=None)
    ap.add_argument('--tag', default='')
    args = ap.parse_args()
    cols = args.width
    t0 = time.time()
    deadline = t0 + 60 * args.minutes

    rects = rectangles_sidevec(ROWS, cols)
    assert rects == verify_narrow.rectangles(ROWS, cols), 'rectangle enumerators disagree'
    n_all, diffs = minimal_differences(rects)

    def var(c, t):
        return 1 + c * len(TYPES) + t
    nbase = cols * len(TYPES)
    pair_types = [t for t, s in enumerate(TYPES) if len(s) == 2]
    single_types = [t for t, s in enumerate(TYPES) if len(s) == 1]
    clauses = []
    for c in range(cols):
        clauses.append([var(c, t) for t in range(len(TYPES))])
        for t1, t2 in combinations(range(len(TYPES)), 2):
            clauses.append([-var(c, t1), -var(c, t2)])
    card = CardEnc.equals(lits=[var(c, t) for c in range(cols) for t in pair_types], bound=6,
                          top_id=nbase, encoding=EncType.seqcounter)
    clauses.extend(card.clauses)
    nvars = max(nbase, card.nv)
    structural = len(clauses)
    srows = None
    if args.singleton_rows:
        srows = {int(r) - 1 for r in args.singleton_rows.split(',')}
        for c in range(cols):
            for t in single_types:
                if TYPES[t][0] not in srows:
                    clauses.append([-var(c, t)])
    dcols = None
    if args.double_columns:
        dcols = {int(x) - 1 for x in args.double_columns.split(',')}
        for c in range(cols):
            for t in (single_types if c in dcols else pair_types):
                clauses.append([-var(c, t)])
    restriction_clauses = len(clauses) - structural
    skipped = 0
    seen = set()
    for d in diffs:
        bycol = {}
        for i in range(d.bit_length()):
            if d >> i & 1:
                bycol.setdefault(i % cols, []).append(i // cols)
        lits = []
        auto = False
        for c, ys in bycol.items():
            if len(ys) >= 3:
                auto = True
                break
            if len(ys) == 2:
                pair = tuple(sorted(ys))
                lits.extend(var(c, t) for t, s in enumerate(TYPES) if s != pair)
            else:
                lits.extend(var(c, t) for t, s in enumerate(TYPES) if ys[0] not in s)
        if auto:
            skipped += 1
            continue
        key = tuple(sorted(lits))
        if key not in seen:
            seen.add(key)
            clauses.append(list(key))
    t_prep = time.time() - t0

    result = {
        'grid': {'rows': ROWS, 'cols': cols}, 'target_size': cols + 6,
        'method': 'SAT model enumeration with blocking clauses, column-type encoding '
                  '(15 types per column, exactly six pair columns, no bipartite shape assumed)',
        'solver': args.solver, 'pysat_version': pysat.__version__,
        'python_version': sys.version.split()[0],
        'rectangles': len(rects), 'rectangle_enumerator': 'corner plus perpendicular side vectors, '
                                                          'equal to verify_narrow.rectangles',
        'distinct_differences': n_all, 'minimal_differences': len(diffs),
        'differences_automatically_satisfied': skipped,
        'variables': nvars, 'clauses': len(clauses), 'structural_clauses': structural,
        'restriction_clauses': restriction_clauses,
        'rectangle_clauses': len(clauses) - structural - restriction_clauses,
        'preparation_seconds': round(t_prep, 2),
        'cap': args.cap, 'wall_limit_minutes': args.minutes,
        'singleton_rows_allowed': sorted(r + 1 for r in srows) if srows else list(range(1, ROWS + 1)),
        'double_columns': sorted(c + 1 for c in dcols) if dcols else None,
        'coordinates': 'one-based (column, row), (1,1) top-left',
        'models': [], 'complete': True, 'status': 'complete',
    }
    with Solver(name=args.solver, bootstrap_with=clauses) as s:
        timer = threading.Timer(max(1.0, deadline - time.time()), s.interrupt)
        timer.start()
        try:
            while True:
                if len(result['models']) >= args.cap:
                    result['complete'] = False
                    result['status'] = f'more than {args.cap} models; enumeration stopped at the cap'
                    break
                sat = s.solve_limited(expect_interrupt=True)
                if sat is None:
                    result['complete'] = False
                    result['status'] = 'wall-clock limit reached; solver interrupted'
                    break
                if not sat:
                    break
                model = s.get_model()
                truth = set(l for l in model if 0 < l <= nbase)
                pts = []
                chosen = []
                for c in range(cols):
                    ts = [t for t in range(len(TYPES)) if var(c, t) in truth]
                    assert len(ts) == 1
                    chosen.append(var(c, ts[0]))
                    pts.extend((c, y) for y in TYPES[ts[0]])
                pts.sort()
                mask = sum(1 << (y * cols + x) for x, y in pts)
                pair = verify_narrow.collision(rects, mask)
                result['models'].append({'points': [[x + 1, y + 1] for x, y in pts],
                                         'verify_narrow_valid': pair is None})
                s.add_clause([-v for v in chosen])
        finally:
            timer.cancel()
    result['model_count'] = len(result['models'])
    result['all_models_verified'] = all(m['verify_narrow_valid'] for m in result['models'])
    result['wall_seconds'] = round(time.time() - t0, 2)
    tag = args.tag or (f'w{cols}' + (f'_srows{args.singleton_rows.replace(",", "")}' if args.singleton_rows else '')
                       + (f'_dcols{args.double_columns.replace(",", "-")}' if args.double_columns else ''))
    out = args.out or os.path.join(DATA_DIR, f'five_row_enum_types_{tag}_{args.solver}.json')
    with open(out, 'w') as f:
        json.dump(result, f, indent=1)
    print(f'width {cols}: {result["model_count"]} models, complete={result["complete"]} '
          f'({result["status"]}), all verified={result["all_models_verified"]}, '
          f'{result["wall_seconds"]} s -> {out}')


if __name__ == '__main__':
    main()
