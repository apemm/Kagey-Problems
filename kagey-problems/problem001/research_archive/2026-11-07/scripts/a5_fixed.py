import os
import sys, time, json
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'jis', 'scripts'))); sys.path.insert(0, ".")
from five_row_dp_wide import Transfer, tilted_templates
h = 5; W = 1 + 16 // 4
templates = tilted_templates(h)
A = (0, 2, 4); B = (1, 3)
edges = sorted(tuple(sorted((a, b))) for a in A for b in B)
dcols = {int(c) - 1 for c in sys.argv[1].split(',')}
prev = None
for m in range(int(sys.argv[2]), int(sys.argv[3]) + 1):
    tr = Transfer(h, W, templates, edges, list(range(h)))
    n, st = tr.count(m, time.time() + 3600, dcols)
    print(m, n, (n / prev) if prev else None, flush=True)
    prev = n
