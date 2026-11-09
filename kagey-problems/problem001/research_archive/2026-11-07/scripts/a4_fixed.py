import sys, time
sys.path.insert(0, ".")
from five_row_dp_wide import Transfer, tilted_templates
from math import factorial
h = 4; W = 1 + 9 // 4
templates = tilted_templates(h)
A = (0, 2); B = (1, 3)
edges = sorted(tuple(sorted((a, b))) for a in A for b in B)
dcols = {19, 39, 59, 79}
rho = 3.351996777310375
for m in range(100, 131, 10):
    tr = Transfer(h, W, templates, edges, list(range(h)))
    n, st = tr.count(m, time.time() + 3600, dcols)
    print(m, n / (factorial(4) * rho ** m), flush=True)
