"""Third check of the six-row collar certificate by the 4-subset rectangle oracle.

Reads a six-row structured SAT result file, takes the first witness whose two-sided
boundary-row collar test passed, and rechecks the witness board and the collar board with
solver/brute.py (every 4-subset of points tested for being a rectangle; validity straight
from the definition, no difference sets). Slow by design.
Usage: python six_row_collar_brute.py RESULT_JSON [collar_key]   (default key row1_both)
"""
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, ROOT)

from solver.brute import grid_points, rectangle_masks, valid


def check(points_one_based, rows, cols):
    t0 = time.time()
    masks, n = rectangle_masks(rows, cols)
    idx = {p: k for k, p in enumerate(grid_points(rows, cols))}
    S = sum(1 << idx[tuple(p)] for p in points_one_based)
    return {'rows': rows, 'cols': cols, 'rectangles': len(masks), 'size': len(points_one_based),
            'valid_by_brute': valid(S, masks), 'seconds': round(time.time() - t0, 1)}


def main():
    path = sys.argv[1]
    key = sys.argv[2] if len(sys.argv) > 2 else 'row1_both'
    recs = json.load(open(path))
    out = []
    for r in recs:
        c = r.get('collar', {}).get(key)
        if not c or not c['valid_by_verify_narrow']:
            continue
        res = {'source': os.path.basename(path), 'partition_zero_based_rows': r['partition_zero_based_rows'],
               'witness_board': check(r['witness'], r['rows'], r['width']),
               'collar_key': key, 'collar_board': check(c['points'], r['rows'], c['width'])}
        print(json.dumps(res), flush=True)
        out.append(res)
        break
    name = os.path.basename(path).replace('.json', f'_brute_{key}.json')
    with open(os.path.join(ROOT, 'jis', 'data', name), 'w') as fh:
        json.dump(out, fh, indent=1)


if __name__ == '__main__':
    main()
