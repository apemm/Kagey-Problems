"""Seven rows: SAT search for a blackout of w+12 points on the 7 x w grid, one row partition.

Reuses the structured encoders of six_row_structured_sat.py with ROWS = 7: twelve doubles on
the edges of K_{3,4} for a chosen partition, each once, a singleton in every other column, and
only the clauses that involve a tilted rectangle. A model is rechecked by verify_narrow.collision
and by the side-vector enumerator, and a valid witness gets the collar test with W_7 = 10
boundary-row singletons per side.

Usage: python seven_row_sat.py WIDTH A|B TRIPLE CAP_SECONDS
TRIPLE is the three-row part, one-based digits, for example 246.
Output: jis/data/seven_row_sat_w{width}_{encoder}_p{TRIPLE}.json.
"""
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)

import six_row_structured_sat as base
import pysat
from verify_narrow import collision, mask, rectangles

base.ROWS = 7
base.COLLAR = 1 + 36 // 4


def main():
    cols = int(sys.argv[1])
    enc = sys.argv[2].upper()
    small = tuple(int(c) - 1 for c in sys.argv[3])
    cap = int(sys.argv[4])
    big = tuple(r for r in range(7) if r not in small)
    encoder, solver = (base.encode_a, 'cadical153') if enc == 'A' else (base.encode_b, 'glucose4')
    t0 = time.time()
    clauses, n, info, _ = encoder(cols, (small, big))
    gen = time.time() - t0
    status, model, dt = base.solve_capped(solver, clauses, cap)
    rec = {'rows': 7, 'width': cols, 'target': cols + 12, 'encoder': enc, 'solver': solver,
           'pysat_version': pysat.__version__, 'partition_zero_based_rows': [list(small), list(big)],
           'status': status, 'encode_seconds': round(gen, 1), 'solve_seconds': round(dt, 1),
           'cap_seconds': cap, **info}
    if model is not None:
        pts = {((v - 1) % cols, (v - 1) // cols) for v in model if 0 < v <= n}
        black = mask(pts, cols)
        rec['witness'] = base.one_based(pts)
        rec['witness_size'] = len(pts)
        rec['witness_valid_by_verify_narrow'] = collision(rectangles(7, cols), black) is None
        rec['witness_valid_by_side_vectors'] = collision(
            base.rectangles_by_sides(7, cols), black) is None
        rec['picture'] = [''.join('#' if (x, y) in pts else '.' for x in range(cols))
                          for y in range(7)]
        if rec['witness_valid_by_verify_narrow']:
            rec['collar'] = base.collar_tests(pts, cols)
    print(json.dumps({k: v for k, v in rec.items() if k not in ('witness', 'collar')}), flush=True)
    path = os.path.join(ROOT, 'jis', 'data',
                        f'seven_row_sat_w{cols}_{enc}_p{sys.argv[3]}.json')
    with open(path, 'w') as fh:
        json.dump(rec, fh, indent=1)


if __name__ == '__main__':
    main()
