import os
"""Is there a valid 6-row board (singletons + doubles from K_{3,3}, each at most once, any number of
doubles >= 2) with two ADJACENT doubles that are disjoint and not parallel ({a,b},{a+-1,b+-1})?
Force the pair at columns 7, 8 of width 16 and ask SAT."""
import sys, json
from itertools import combinations
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')))
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'jis', 'scripts')))
import six_row_structured_sat as base
from verify_narrow import rectangles, axis_rectangles, collision, mask
from pysat.solvers import Solver

H, cols = 6, 16
base.ROWS = H
A, B = (0, 2, 4), (1, 3, 5)
edges = [(min(a, b), max(a, b)) for a in A for b in B]
res = {}
for e1 in edges:
    for e2 in edges:
        if set(e1) & set(e2):
            continue
        par = abs(e1[0] - e2[0]) == 1 and abs(e1[1] - e2[1]) == 1 and (e1[0] - e2[0]) == (e1[1] - e2[1])
        if par:
            continue
        var = {r * cols + x: r * cols + x + 1 for r in range(H) for x in range(cols)}
        n = H * cols
        types = [(r,) for r in range(H)] + [tuple(ed) for ed in edges]
        t = {(x, j): n + x * len(types) + j + 1 for x in range(cols) for j in range(len(types))}
        cl = []
        for x in range(cols):
            cl.append([t[x, j] for j in range(len(types))])
            for j, k in combinations(range(len(types)), 2):
                cl.append([-t[x, j], -t[x, k]])
            for r in range(H):
                holders = [t[x, j] for j, ty in enumerate(types) if r in ty]
                for hh in holders:
                    cl.append([-hh, var[r * cols + x]])
                cl.append([-var[r * cols + x]] + holders)
        for j in range(H, len(types)):
            for x, y in combinations(range(cols), 2):
                cl.append([-t[x, j], -t[y, j]])
        cl.append([t[7, H + edges.index(e1)]]); cl.append([t[8, H + edges.index(e2)]])
        rects = rectangles(H, cols); axis = set(axis_rectangles(H, cols))
        flags = [r not in axis for r in rects]
        pc, full = base.tilted_clauses(rects, flags, cols, set(edges), var)
        cl += pc
        for c in full:
            cl.append([-v for v in c])
        with Solver(name='cadical153', bootstrap_with=cl) as s:
            ok = s.solve()
            w = None
            if ok:
                m = set(l for l in s.get_model() if 0 < l <= n)
                pts = {((v - 1) % cols, (v - 1) // cols) for v in m}
                w = ','.join(''.join(str(y + 1) for y in range(H) if (x, y) in pts) for x in range(cols))
                assert collision(rects, mask(pts, cols)) is None
        res[f'{e1[0]+1}{e1[1]+1}|{e2[0]+1}{e2[1]+1}'] = w
        print(e1, e2, 'SAT' if ok else 'UNSAT', w, flush=True)
