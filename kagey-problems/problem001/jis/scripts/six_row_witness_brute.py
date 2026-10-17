"""Third check of six-row witnesses and collar boards by the 4-subset rectangle oracle.

Reads six-row structured SAT result files (six_row_sat_w{w}_{A,B}.json), and for every
record with a witness rechecks the witness board, and every collar board that passed the
two enumerator checks, with solver/brute.py: rectangles are found by testing every
4-subset of points, and validity is read straight from the definition (injective
presentations), with no difference sets and no code shared with verify_narrow.py or the
SAT encoders. Slow by design; a wall-clock cap stops the run and marks the rest unchecked.

Points in the files and in the output are one-based (column, row), (1,1) top left.
Usage: python six_row_witness_brute.py OUT_JSON [CAP_SECONDS] RESULT_JSON [RESULT_JSON ...]
"""
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, ROOT)

from solver.brute import grid_points, rectangle_masks, valid

MASKS = {}


def check(points_one_based, rows, cols):
    t0 = time.time()
    if (rows, cols) not in MASKS:
        MASKS[rows, cols] = rectangle_masks(rows, cols)
    masks, n = MASKS[rows, cols]
    idx = {p: k for k, p in enumerate(grid_points(rows, cols))}
    pts = {tuple(p) for p in points_one_based}
    S = sum(1 << idx[p] for p in pts)
    return {'rows': rows, 'cols': cols, 'rectangles': len(masks), 'size': len(pts),
            'valid_by_brute': valid(S, masks), 'seconds': round(time.time() - t0, 1)}


def main():
    out_path = sys.argv[1]
    args = sys.argv[2:]
    cap = 1800
    if args and args[0].isdigit():
        cap = int(args[0])
        args = args[1:]
    start = time.time()
    out = {'cap_seconds': cap, 'boards': [], 'unchecked': []}
    for path in args:
        recs = json.load(open(path))
        for r in recs:
            if 'witness' not in r:
                continue
            jobs = [('witness', r['width'], r['witness'])]
            for key, c in r.get('collar', {}).items():
                if c['valid_by_verify_narrow'] and c['valid_by_side_vectors']:
                    jobs.append((key, c['width'], c['points']))
            for key, w, pts in jobs:
                label = {'source': os.path.basename(path),
                         'partition_zero_based_rows': r['partition_zero_based_rows'],
                         'board': key}
                if time.time() - start > cap:
                    out['unchecked'].append(label)
                    continue
                res = {**label, **check(pts, r['rows'], w)}
                print(json.dumps(res), flush=True)
                out['boards'].append(res)
    out['total_seconds'] = round(time.time() - start, 1)
    with open(out_path, 'w') as fh:
        json.dump(out, fh, indent=1)
    print(f"done: {len(out['boards'])} boards checked, {len(out['unchecked'])} unchecked, "
          f"{out['total_seconds']} s", flush=True)


if __name__ == '__main__':
    main()
