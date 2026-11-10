"""Calibration of equality_sat.py against known exact thresholds.

Known: equality first occurs at width 6, 8, 15 for heights 4, 5, 6. The encoder
must return UNSAT for every balanced partition one column below, and SAT for
some partition at the threshold. It must also accept the four stored 7 x 21
boards (every clause satisfied) and report the sizes of the 8 and 9 row data."""
import json, time
from equality_sat import *
from rectlib import check_board
from boards import load_all

out = {}
for h, m0 in ((4, 6), (5, 8), (6, 15)):
    g = Geometry(h)
    for w in (m0 - 1, m0):
        res = []
        for A in partitions(h):
            s = supports(g, A)
            cl, nv = encode(h, w, A, s)
            st, m, sec, _ = solve(cl, 600)
            rec = {'A_rows': [r + 1 for r in A], 'status': st, 'seconds': round(sec, 2)}
            if m:
                b = board_from_model(h, w, m)
                rec['word'] = word(b); rec['check'] = check_board(h, b)['valid']
            res.append(rec)
        out[f'h{h}_w{w}'] = res
        print(h, w, [(r['A_rows'], r['status'], r.get('check')) for r in res], flush=True)

g = Geometry(7); A = (1, 3, 5); s = supports(g, A)
cl, nv = encode(7, 21, A, s, anchor=False)
ok = []
for name, h, cols in load_all():
    if h != 7:
        continue
    black = {c * 7 + r for c, col in enumerate(cols) for r in col}   # variable of (c, row r) is c*7 + r
    geom = [c for c in cl if all(l < 0 and -l <= 21 * 7 for l in c)]
    ok.append(all(any(-l not in black for l in c) for c in geom))
out['h7_w21_stored_boards_satisfy_all_geometry_clauses'] = ok
out['h7_w21_geometry_clauses'] = len(geom)
print(ok, len(geom), flush=True)

for h in (8, 9):
    t = time.time(); g = Geometry(h)
    A = tuple(r for r in range(h) if r % 2 == 1)
    s = supports(g, A)
    out[f'h{h}'] = {'max_tilted_columns': g.span, 'pair_supports_raw': len(g.pair),
                    'minimal_supports_parity': len(s), 'partition_classes': len(partitions(h)),
                    'seconds': round(time.time() - t, 1)}
    print(h, out[f'h{h}'], flush=True)
(HERE / 'calibrate_encoder.json').write_text(json.dumps(out, indent=1))
