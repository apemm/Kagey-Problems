"""The six-row family 16,36,25,12,1^k,23,34,45,56 (black rows of each column, one-based) of
width m = k+8 with m+8 points. Checked for k = 0..11 by verify_narrow.collision and by the
side-vector enumerator, and for k = 4, 5, 6 (widths 12, 13, 14) also by solver/brute.py.
Output: jis/data/six_row_excess8_family.json.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, ROOT)
sys.path.insert(0, HERE)
from verify_narrow import collision, mask, rectangles
from six_row_structured_sat import rectangles_by_sides
from six_row_witness_brute import check

out = []
for k in range(12):
    ws = ['16', '36', '25', '12'] + ['1'] * k + ['23', '34', '45', '56']
    m = len(ws)
    pts = [(x, int(c) - 1) for x, w in enumerate(ws) for c in w]
    black = mask(pts, m)
    rec = {'k': k, 'width': m, 'points': len(pts), 'word': ','.join(ws),
           'valid_by_verify_narrow': collision(rectangles(6, m), black) is None,
           'valid_by_side_vectors': collision(rectangles_by_sides(6, m), black) is None}
    if m in (12, 13, 14):
        rec['brute'] = check([(x + 1, y + 1) for x, y in pts], 6, m)
    print(json.dumps(rec), flush=True)
    out.append(rec)
json.dump(out, open(os.path.join(ROOT, 'jis', 'data', 'six_row_excess8_family.json'), 'w'), indent=1)
