r"""Five rows, column-type SAT search for a blackout of m+6 points (method B).

This is a second encoding, written separately from five_row_structured_sat.py, and run on
a different solver.  It uses a weaker hypothesis than the full equality structure: every
column has one or two black points, and exactly six columns have two.  (Any valid
blackout of m+6 points on five rows has this form; the row-pair structure K_{2,3} is NOT
imposed here, the clauses enforce it on their own.)

Encoding.  One variable per (column, type) with 15 types per column: the five singleton
rows and the ten row pairs.  Exactly one type per column.  Exactly six double types in
all (pysat.card, totalizer).  For every unordered pair of distinct rectangles with
symmetric difference D, the clause "some column of D has a type that does not contain
the rows of D in that column" (that is, D is not entirely black); pairs with three or
more points of D in one column are satisfied automatically and are skipped.  No superset
pruning.

Rectangles are enumerated from a corner and two perpendicular integer side vectors, a
different method from the equal-diagonal enumerator of verify_narrow.py; the two counts
are compared.  A satisfying assignment is decoded to a point set and rechecked twice: by
this script's own presentation test and by verify_narrow.collision.

Every instance runs in a child process with a hard wall-clock cap.  Internally the
columns and rows are zero-based; the JSON output is ONE-BASED (column, row), (1, 1) top
left.

Usage:
  python five_row_column_sat.py --widths 8 9 10 --solver glucose4 --cap 1800
                                --out ../data/five_row_column_glucose4.json
"""
import argparse
import json
import os
import subprocess
import sys
import time
from itertools import combinations
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, REPO)
import verify_narrow  # noqa: E402

H = 5
SINGLES = [(r,) for r in range(H)]
DOUBLES = [pair for pair in combinations(range(H), 2)]
TYPES = SINGLES + DOUBLES          # 15 column types


def rectangles_by_sides(h, m):
    """Rectangles with corners on the h x m grid, as frozensets of (col, row).

    A rectangle is a corner p, a side u = (a, b) and a perpendicular side
    v = t * (-b, a) / gcd(a, b), t a nonzero integer.  Every rectangle arises; the
    frozenset removes repeats.
    """
    found = set()
    for a in range(-(m - 1), m):
        for b in range(0, h):
            if (a, b) == (0, 0) or (b == 0 and a < 0):
                continue
            g = gcd(abs(a), b)
            pa, pb = -b // g, a // g
            for t in range(1, max(h, m)):
                vx, vy = t * pa, t * pb
                if abs(vx) >= m or abs(vy) >= h:
                    break
                for x in range(m):
                    for y in range(h):
                        corners = ((x, y), (x + a, y + b), (x + vx, y + vy),
                                   (x + a + vx, y + b + vy))
                        if all(0 <= cx < m and 0 <= cy < h for cx, cy in corners):
                            found.add(frozenset(corners))
    return found


def to_mask(corners, m):
    return sum(1 << (y * m + x) for x, y in corners)


def var(col, t):
    return col * len(TYPES) + t + 1


def build(m):
    from pysat.card import CardEnc, EncType
    rects = rectangles_by_sides(H, m)
    masks = sorted(to_mask(r, m) for r in rects)
    check = verify_narrow.rectangles(H, m)
    assert masks == check, 'the two rectangle enumerators disagree'
    n_vars = m * len(TYPES)
    clauses = []
    for c in range(m):
        clauses.append([var(c, t) for t in range(len(TYPES))])
        for t, u in combinations(range(len(TYPES)), 2):
            clauses.append([-var(c, t), -var(c, u)])
    double_lits = [var(c, t) for c in range(m) for t in range(len(SINGLES), len(TYPES))]
    card = CardEnc.equals(lits=double_lits, bound=6, top_id=n_vars, encoding=EncType.totalizer)
    clauses.extend(card.clauses)
    top = max(n_vars, card.nv)
    structural = len(clauses)
    # types that do not contain a given row set, per row set
    not_containing = {}
    for rows in [(r,) for r in range(H)] + DOUBLES:
        not_containing[rows] = [t for t, ty in enumerate(TYPES) if not set(rows) <= set(ty)]
    colmask = [sum(1 << (y * m + x) for y in range(H)) for x in range(m)]
    seen = set()
    skipped = 0
    for a, b in combinations(masks, 2):
        d = a ^ b
        if d in seen:
            continue
        seen.add(d)
        lits = []
        ok = True
        for x in range(m):
            dx = d & colmask[x]
            if not dx:
                continue
            rows = tuple(y for y in range(H) if dx >> (y * m + x) & 1)
            if len(rows) >= 3:
                ok = False
                break
            lits.extend(var(x, t) for t in not_containing[rows])
        if ok:
            clauses.append(lits)
        else:
            skipped += 1
    info = dict(rectangles=len(masks), distinct_differences=len(seen),
                differences_skipped_three_in_a_column=skipped,
                structural_clauses=structural, clauses=len(clauses), variables=top)
    return clauses, info, masks, rects


def own_valid(points, rects):
    """Definitional check: all presentations (visible corner sets) distinct."""
    black = set(points)
    seen = set()
    for r in rects:
        vis = frozenset(p for p in r if p not in black)
        if vis in seen:
            return False
        seen.add(vis)
    return True


def worker(args):
    from pysat.solvers import Solver
    m = args.width
    t0 = time.time()
    clauses, info, masks, rects = build(m)
    t_build = time.time() - t0
    t1 = time.time()
    boards = []
    with Solver(name=args.solver, bootstrap_with=clauses) as s:
        sat = s.solve()
        model = s.get_model() if sat else None
        while model is not None:
            chosen = [var(c, t) for c in range(m) for t in range(len(TYPES))
                      if model[var(c, t) - 1] > 0]
            assert len(chosen) == m
            boards.append(sorted((( v - 1) // len(TYPES), r)
                                 for v in chosen for r in TYPES[(v - 1) % len(TYPES)]))
            if not args.count or len(boards) >= args.count:
                break
            s.add_clause([-v for v in chosen])          # block this board
            model = s.get_model() if s.solve() else None
    t_solve = time.time() - t1
    result = dict(width=m, solver=args.solver, status='SAT' if sat else 'UNSAT',
                  build_seconds=round(t_build, 2), solve_seconds=round(t_solve, 2), **info)
    if sat:
        pts = boards[0]
        assert len(pts) == m + 6
        if args.count:
            result['models_found'] = len(boards)
            result['count_exhausted'] = len(boards) < args.count
            result['models_failing_recheck'] = sum(
                verify_narrow.collision(masks, verify_narrow.mask(b, m)) is not None
                for b in boards)
            result['models_one_based'] = [[[c + 1, r + 1] for c, r in b] for b in boards]
        result['witness_one_based'] = [[c + 1, r + 1] for c, r in pts]
        result['witness_valid_by_own_check'] = own_valid(pts, rects)
        result['witness_valid_by_verify_narrow'] = \
            verify_narrow.collision(masks, verify_narrow.mask(pts, m)) is None
        result['witness_picture'] = [''.join('#' if (c, r) in set(pts) else '.'
                                             for c in range(m)) for r in range(H)]
        doubles = [tuple(r + 1 for r in range(H) if (c, r) in set(pts))
                   for c in range(m) if sum((c, r) in set(pts) for r in range(H)) == 2]
        result['double_row_pairs_one_based'] = doubles
    print(json.dumps(result))


def run_instance(args, m):
    cmd = [sys.executable, '-I', os.path.abspath(__file__), '--worker', '--width', str(m),
           '--solver', args.solver]
    if args.count:
        cmd += ['--count', str(args.count)]
    t0 = time.time()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=args.cap)
    except subprocess.TimeoutExpired:
        return dict(width=m, solver=args.solver, status='unresolved',
                    wall_seconds=round(time.time() - t0, 1), cap_seconds=args.cap)
    wall = time.time() - t0
    if proc.returncode != 0:
        return dict(width=m, solver=args.solver, status='error',
                    wall_seconds=round(wall, 1), stderr=proc.stderr[-2000:])
    out = json.loads(proc.stdout.strip().splitlines()[-1])
    out['wall_seconds'] = round(wall, 1)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--widths', type=int, nargs='+', default=list(range(8, 21)))
    ap.add_argument('--solver', default='glucose4')
    ap.add_argument('--cap', type=int, default=1800)
    ap.add_argument('--count', type=int, default=0,
                    help='enumerate up to this many boards with blocking clauses')
    ap.add_argument('--out', default=None)
    ap.add_argument('--worker', action='store_true')
    ap.add_argument('--width', type=int)
    args = ap.parse_args()
    if args.worker:
        worker(args)
        return
    import pysat
    results = dict(method='column-type SAT, columns of size 1 or 2, six doubles (method B)',
                   solver=args.solver, pysat_version=pysat.__version__,
                   python_version=sys.version.split()[0], cap_seconds=args.cap,
                   coordinates='one-based (column,row)', instances=[])
    for m in args.widths:
        r = run_instance(args, m)
        results['instances'].append(r)
        print(f"width {m}: {r['status']} wall {r.get('wall_seconds')}s "
              f"clauses {r.get('clauses')} vars {r.get('variables')} "
              f"valid {r.get('witness_valid_by_verify_narrow')}" +
              (f" models {r.get('models_found')} exhausted {r.get('count_exhausted')}"
               if args.count else ''), flush=True)
        if args.out:
            with open(args.out, 'w') as f:
                json.dump(results, f, indent=1)


if __name__ == '__main__':
    main()
