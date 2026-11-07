"""Third check of the seven-row witnesses of widths 24 to 28, and of the width-28 collar board
(10 columns black only in row 7 on the left), by solver/brute.py (every 4-subset of points).
Output: jis/data/seven_row_witness_brute.json."""
import json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from six_row_witness_brute import check
D = os.path.join(HERE, '..', 'data')
out = []
for name in ('seven_row_sat_w24_A_p246.json', 'seven_row_sat_w25_A_p246.json', 'seven_row_sat_w26_A_p246.json', 'seven_row_sat_w27_A_p147.json',
             'seven_row_sat_w28_A_p246.json'):
    r = json.load(open(os.path.join(D, name)))
    out.append({'source': name, 'board': 'witness', **check(r['witness'], 7, r['width'])})
    print(out[-1], flush=True)
    if name.endswith('w28_A_p246.json'):
        c = r['collar']['row7_left']
        out.append({'source': name, 'board': 'row7_left collar', **check(c['points'], 7, c['width'])})
        print(out[-1], flush=True)
json.dump(out, open(os.path.join(D, 'seven_row_witness_brute.json'), 'w'), indent=1)
