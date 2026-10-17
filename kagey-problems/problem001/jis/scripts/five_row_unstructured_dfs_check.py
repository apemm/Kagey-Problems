"""Solver-free, structure-free search for blackouts of m+6 points on 5 x m, m = 5, 6, 7.

Columns are walked left to right, each column any of the 32 subsets of the
five rows, with two prunings only: a prefix is abandoned as soon as two
rectangles inside it have the same visible corners (restriction of a valid
blackout to an interval of columns is valid), and as soon as five points per
remaining column cannot reach the target.  No structure theorem and no row
bound is used, so a count of zero at the target m+6 is a direct proof that
f(5,m) <= m+5.  The search also records the largest valid blackout it meets
below the target, which is the value f(5,m) itself.

Rectangles and the presentation test come from five_row_geometry_check.
Each width runs under a wall-clock cap and is recorded as unresolved if the
cap is hit.  Output: jis/data/five_row_unstructured_dfs_check.json.

Usage: five_row_unstructured_dfs_check.py [width ...]   (default 5 6 7)
"""
import json
import os
import sys
import time

from five_row_geometry_check import rectangles_by_max_column, one_based_from_mask

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, '..', 'data')
ROWS = 5
CAP_SECONDS = 1200


class Timeout(Exception):
    pass


def search(cols, target, deadline):
    groups = rectangles_by_max_column(ROWS, cols)
    column_masks = [sum(1 << (r * cols) for r in range(ROWS) if s >> r & 1) for s in range(32)]
    seen = {}
    stats = {'nodes': 0, 'hits': 0, 'best': 0, 'best_board': 0}

    def place(c, black, size):
        stats['nodes'] += 1
        if stats['nodes'] % 200000 == 0 and time.time() > deadline:
            raise Timeout
        if size > stats['best']:
            stats['best'], stats['best_board'] = size, black
        if c == cols:
            if size >= target:
                stats['hits'] += 1
            return
        if size + ROWS * (cols - c) < target:
            return
        for colmask in column_masks:
            nb = black | (colmask << c)
            added = []
            ok = True
            for r in groups[c]:
                shown = r & ~nb
                if shown in seen:
                    ok = False
                    break
                seen[shown] = 1
                added.append(shown)
            if ok:
                place(c + 1, nb, size + colmask.bit_count())
            for shown in added:
                del seen[shown]

    place(0, 0, 0)
    return stats


def main():
    widths = [int(a) for a in sys.argv[1:]] or [5, 6, 7]
    out = {'method': 'column-by-column search over all 32 column subsets with prefix pruning, no structure used',
           'solver': 'none', 'python_version': sys.version.split()[0], 'cap_seconds': CAP_SECONDS,
           'coordinates': 'one-based (column,row)', 'widths': {}}
    path = os.path.join(DATA, 'five_row_unstructured_dfs_check.json')
    for m in widths:
        t0 = time.time()
        target = m + 6
        rec = {'width': m, 'target_points': target}
        try:
            st = search(m, target, t0 + CAP_SECONDS)
            rec.update({'status': 'complete', 'boards_with_at_least_target': st['hits'], 'nodes': st['nodes'],
                        'largest_valid_blackout_met': st['best'],
                        'largest_board_one_based': one_based_from_mask(st['best_board'], ROWS, m)})
        except Timeout:
            rec['status'] = 'unresolved'
        rec['seconds'] = round(time.time() - t0, 1)
        out['widths'][str(m)] = rec
        print(json.dumps(rec), flush=True)
        with open(path, 'w') as f:
            json.dump(out, f, indent=1)


if __name__ == '__main__':
    main()
