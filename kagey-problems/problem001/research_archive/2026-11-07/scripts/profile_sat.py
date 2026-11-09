"""Lower bounds for f(h, W): exactly e doubles, each an edge of K_{A,B} used at most once, every other
column a singleton. SAT (encoder A style). Usage: python profile_sat.py H W e PART CAP"""
import sys, os, json, time
from itertools import combinations
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')))
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'jis', 'scripts')))
import six_row_structured_sat as base
from pysat.card import CardEnc, EncType
from verify_narrow import collision, mask, rectangles, axis_rectangles


def main():
    H, Wd, e = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    A = tuple(int(c) - 1 for c in sys.argv[4]); cap = int(sys.argv[5])
    base.ROWS = H
    B = tuple(r for r in range(H) if r not in A)
    edges = [(min(a, b), max(a, b)) for a in A for b in B]
    edge_set = set(edges)
    cols = Wd
    var = {r * cols + x: r * cols + x + 1 for r in range(H) for x in range(cols)}
    n = H * cols
    types = [(r,) for r in range(H)] + [tuple(ed) for ed in edges]
    t = {(x, j): n + x * len(types) + j + 1 for x in range(cols) for j in range(len(types))}
    top = n + cols * len(types)
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
    dl = [t[x, j] for x in range(cols) for j in range(H, len(types))]
    card = CardEnc.equals(lits=dl, bound=e, top_id=top, encoding=EncType.seqcounter)
    cl += card.clauses; top = max(top, card.nv)
    rects = rectangles(H, cols)
    axis = set(axis_rectangles(H, cols))
    flags = [r not in axis for r in rects]
    pc, full = base.tilted_clauses(rects, flags, cols, edge_set, var)
    # feasibility filter in tilted_clauses assumes each edge at most once: still sound here
    cl += pc
    for corners in full:
        cl.append([-v for v in corners])
    status, model, dt = base.solve_capped('cadical153', cl, cap)
    rec = {'h': H, 'w': Wd, 'e': e, 'A': [a + 1 for a in A], 'status': status, 'solve_s': round(dt)}
    if model is not None:
        pts = {((v - 1) % cols, (v - 1) // cols) for v in model if 0 < v <= n}
        rec['valid'] = collision(rects, mask(pts, cols)) is None
        rec['size'] = len(pts)
        rec['word'] = ','.join(''.join(str(y + 1) for y in range(H) if (x, y) in pts) for x in range(cols))
    print(json.dumps(rec), flush=True)
    json.dump(rec, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), f'prof_h{H}_w{Wd}_e{e}_p{sys.argv[4]}.json'), 'w'))


if __name__ == '__main__':
    main()
