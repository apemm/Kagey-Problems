r"""Five rows: a width-w blackout of w+6 points that extends by boundary-row singletons.

Searches, with the structured encoding of five_row_structured_sat.py, for a blackout of
width w + p whose last p columns (or first p columns, with --side left) are singletons
in a chosen boundary row (row 1, the top, or row 5, the bottom).  The first w columns
then form a valid blackout of w+6 points (restriction preserves validity), and the test
board shows that appending p such singleton columns keeps it valid.  With p = 5 (the
tilted span bound W_5 = 1 + floor(16/4) at height five) the finite-collar theorem of
the research notes says that the board extended by ANY number of such columns is valid,
which gives f(5,m) = m+6 for every m >= w from a single certificate.

Independently of that theorem, this script checks the extended boards directly at every
width from w up to --check (default 80) with verify_narrow.collision, and again with a
separately written presentation test over rectangles enumerated from perpendicular
sides.  Both checks are reported.

Coordinates in the JSON output are ONE-BASED (column, row), (1, 1) top left.

Usage:
  python five_row_collar_family.py --base 8 --pad 5 --row 1 --side right
                                   --out ../data/five_row_collar_family.json
"""
import argparse
import json
import os
import sys
import time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, REPO)
sys.path.insert(0, HERE)
import verify_narrow  # noqa: E402
from five_row_structured_sat import PARTITIONS, ROWS, build_instance, decode  # noqa: E402
from five_row_column_sat import rectangles_by_sides, own_valid  # noqa: E402


def find_family(base, pad, row, side, solver):
    """Try every partition; return the first board whose padding columns are singletons."""
    from pysat.solvers import Solver
    m = base + pad
    pad_cols = list(range(base, m)) if side == 'right' else list(range(pad))
    tried = []
    for part in PARTITIONS:
        clauses, info, rects = build_instance(m, part)
        units = []
        for c in pad_cols:
            for r in range(ROWS):
                v = c * ROWS + r + 1
                units.append([v] if r == row else [-v])
        t0 = time.time()
        with Solver(name=solver, bootstrap_with=clauses + units) as s:
            sat = s.solve()
            model = s.get_model() if sat else None
        tried.append(dict(partition_rows_one_based=[p + 1 for p in part],
                          status='SAT' if sat else 'UNSAT', seconds=round(time.time() - t0, 2),
                          clauses=len(clauses) + len(units), variables=info['variables']))
        if sat:
            pts = decode(model, m)
            assert verify_narrow.collision(rects, verify_narrow.mask(pts, m)) is None
            board = [(c, r) for c, r in pts if c not in pad_cols]
            if side == 'left':
                board = [(c - pad, r) for c, r in board]
            return board, tried
    return None, tried


def extended(board, base, k, row, side):
    if side == 'right':
        return sorted(board + [(base + i, row) for i in range(k)])
    return sorted([(c + k, r) for c, r in board] + [(i, row) for i in range(k)])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--base', type=int, default=8)
    ap.add_argument('--pad', type=int, default=5)
    ap.add_argument('--row', type=int, default=1, help='one-based boundary row, 1 or 5')
    ap.add_argument('--side', default='right', choices=['right', 'left'])
    ap.add_argument('--check', type=int, default=80)
    ap.add_argument('--solver', default='cadical153')
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    row0 = args.row - 1
    t0 = time.time()
    board, tried = find_family(args.base, args.pad, row0, args.side, args.solver)
    out = dict(method='structured SAT with forced singleton collar, then direct checks',
               base_width=args.base, pad=args.pad, boundary_row_one_based=args.row,
               side=args.side, solver=args.solver, partitions_tried=tried,
               coordinates='one-based (column,row)', search_seconds=round(time.time() - t0, 1))
    if board is None:
        out['status'] = 'no such board'
    else:
        out['status'] = 'found'
        out['board_one_based'] = [[c + 1, r + 1] for c, r in board]
        out['board_picture'] = [''.join('#' if (c, r) in set(board) else '.'
                                        for c in range(args.base)) for r in range(ROWS)]
        checks = []
        all_ok = True
        for m in range(args.base, args.check + 1):
            k = m - args.base
            pts = extended(board, args.base, k, row0, args.side)
            assert len(pts) == m + 6
            rects = verify_narrow.rectangles(ROWS, m)
            ok1 = verify_narrow.collision(rects, verify_narrow.mask(pts, m)) is None
            side_rects = rectangles_by_sides(ROWS, m)
            ok2 = own_valid(pts, side_rects)
            assert len(side_rects) == len(rects)
            checks.append(dict(width=m, valid_by_verify_narrow=ok1, valid_by_side_enumerator=ok2,
                               rectangles=len(rects)))
            all_ok = all_ok and ok1 and ok2
            print(f"width {m}: {ok1} {ok2} ({len(rects)} rectangles)", flush=True)
        out['extension_checks'] = checks
        out['all_extensions_valid_through_check_width'] = all_ok
    out['total_seconds'] = round(time.time() - t0, 1)
    if args.out:
        with open(args.out, 'w') as f:
            json.dump(out, f, indent=1)
    print(json.dumps({k: v for k, v in out.items() if k not in ('extension_checks',)}, indent=1))


if __name__ == '__main__':
    main()
