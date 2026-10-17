"""Case split for a hard small cell: is there a valid blackout of k points on h x m?

With k > 2m some column has at least three black points. The j-th case (j = 1..m) is:
columns 1..j-1 have at most two black points and column j has at least three. The cases are
disjoint and cover every blackout of k points, so the instance is unsatisfiable exactly when
all m cases are. Each case is run with both encodings of small_cells_sat.py (A: minimal
differences, sequential counter, cadical153; B: corner-sharing pairs plus full-rectangle
indicators, totalizer, glucose4), each capped at 30 minutes.

Output: jis/data/small_cells_split_{h}x{m}_b{k}_case{j}_{A|B}.json.
Usage: python small_cells_split.py HxM k j A|B
"""
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)

import pysat
from pysat.card import CardEnc, EncType

from small_cells_sat import encoding_a, encoding_b, model_to_mask, points_one_based, solve_capped
from verify_narrow import collision, rectangles


def main():
    rows, cols = map(int, sys.argv[1].split('x'))
    k = int(sys.argv[2])
    j = int(sys.argv[3])
    enc = sys.argv[4].upper()
    encoder, solver = (encoding_a, 'cadical153') if enc == 'A' else (encoding_b, 'glucose4')
    t0 = time.time()
    clauses, n, info = encoder(rows, cols, k)
    top = max(abs(l) for c in clauses for l in c)
    for x in range(1, j + 1):
        lits = [(y - 1) * cols + (x - 1) + 1 for y in range(1, rows + 1)]
        if x < j:
            card = CardEnc.atmost(lits=lits, bound=2, top_id=top, encoding=EncType.seqcounter)
        else:
            card = CardEnc.atleast(lits=lits, bound=3, top_id=top, encoding=EncType.seqcounter)
        clauses += card.clauses
        top = max(top, card.nv)
    gen = time.time() - t0
    status, model, dt = solve_capped(solver, clauses)
    rec = {'grid': f'{rows}x{cols}', 'bound': k, 'case': j,
           'case_meaning': f'columns 1..{j - 1} have at most 2 black points, column {j} at least 3',
           'encoding': enc, 'solver': solver, 'pysat_version': pysat.__version__, 'status': status,
           'encode_seconds': round(gen, 2), 'solve_seconds': round(dt, 2),
           'variables': top, 'clauses': len(clauses), **info}
    if model is not None:
        black = model_to_mask(model, n)
        rec['witness'] = points_one_based(black, cols)
        rec['witness_size'] = black.bit_count()
        rec['witness_valid_by_verify_narrow'] = collision(rectangles(rows, cols), black) is None
    print(json.dumps(rec), flush=True)
    name = f'small_cells_split_{rows}x{cols}_b{k}_case{j}_{enc}.json'
    with open(os.path.join(ROOT, 'jis', 'data', name), 'w') as fh:
        json.dump(rec, fh, indent=1)


if __name__ == '__main__':
    main()
