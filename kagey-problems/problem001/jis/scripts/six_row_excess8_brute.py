"""Third check of the six-row witnesses with w+8 points (w = 12, 13, 14) by the 4-subset oracle.

For each result file six_row_excess8_w{w}_{A,B}.json, the first SAT witness is rechecked with
solver/brute.py (rectangles from every 4-subset of points, validity straight from the
definition), sharing no code with verify_narrow.py or the encoders.
Usage: python six_row_excess8_brute.py OUT_JSON RESULT_JSON [RESULT_JSON ...]
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from six_row_witness_brute import check

out = []
for path in sys.argv[2:]:
    for r in json.load(open(path)):
        if 'witness' in r:
            res = {'source': os.path.basename(path), 'family': r['family'], 'case': r['case'],
                   'witness': r['witness'], **check(r['witness'], 6, r['width'])}
            print(json.dumps({k: v for k, v in res.items() if k != 'witness'}), flush=True)
            out.append(res)
            break
json.dump(out, open(sys.argv[1], 'w'), indent=1)
