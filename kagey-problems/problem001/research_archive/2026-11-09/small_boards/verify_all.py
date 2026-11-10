"""Independent re-verification of every stored board used in this folder.
Diagonal method (rectlib.check_board); the total rectangle count is compared
with a separate count from perpendicular side vectors."""
import json, time
from boards import load_all, load_extra, HERE
from rectlib import check_board, count_rectangles_by_sides

out = []
for name, h, cols in load_all() + load_extra():
    t = time.time()
    r = check_board(h, cols)
    r['name'] = name
    r['doubles'] = sum(len(c) == 2 for c in cols)
    r['equality'] = r['black'] == len(cols) + (h * h) // 4 and r['doubles'] == (h * h) // 4
    r['rectangle_count_by_sides'] = count_rectangles_by_sides(h, len(cols))
    r['counts_agree'] = r['rectangle_count_by_sides'] == r['rectangles']
    r['seconds'] = round(time.time() - t, 1)
    out.append(r)
    print(name, r['valid'], r['equality'], r['rectangles'], r['counts_agree'], r['seconds'], flush=True)
(HERE / 'verify_all.json').write_text(json.dumps(out, indent=1))
