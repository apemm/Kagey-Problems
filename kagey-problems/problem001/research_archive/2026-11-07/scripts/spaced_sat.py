"""Regular-spacing test: h rows, the q_h doubles of K_{A,B} at columns L + j(g+1) (j = 0..q-1), singletons
(any row) elsewhere, L lead singletons and R trailing singletons. SAT on encoder A of
six_row_structured_sat with extra unit/OR clauses fixing which columns are doubles.
Usage: python spaced_sat.py H g L R PART CAP"""
import sys, os, json, time
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')))
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'jis', 'scripts')))
import six_row_structured_sat as base
from verify_narrow import collision, mask, rectangles

def main():
    H, g, L, R = map(int, sys.argv[1:5])
    A = tuple(int(c) - 1 for c in sys.argv[5]); cap = int(sys.argv[6]); rule = sys.argv[7] if len(sys.argv) > 7 else 'none'
    base.ROWS = H; base.COLLAR = 1 + (H - 1) ** 2 // 4
    B = tuple(r for r in range(H) if r not in A)
    q = len(A) * len(B)
    W = L + q + (q - 1) * g + R
    if g < 0:      # alternating gaps 1 and 2 (density 2/5)
        dpos = set(); x = L
        for j in range(q):
            dpos.add(x); x += 2 if j % 2 == 0 else 3
        W = max(dpos) + 1 + R
    else:
        dpos = {L + j * (g + 1) for j in range(q)}
    clauses, n, info, _ = base.encode_a(W, (A, B))
    ntypes = H + q
    tvar = lambda x, j: n + x * ntypes + j + 1          # matches encode_a numbering
    for x in range(W):
        if x in dpos:
            clauses.append([tvar(x, j) for j in range(H, ntypes)])
        else:
            clauses.append([tvar(x, j) for j in range(H)])
    edges = [(min(a, b), max(a, b)) for a in A for b in B]
    dl = sorted(dpos)
    for x in range(W):
        if x in dpos:
            continue
        prev = max([p for p in dl if p < x], default=None)
        nxt = min([p for p in dl if p > x], default=None)
        nb = [p for p in ((prev,) if rule in ('prev', 'same') else (prev, nxt)) if p is not None]
        if rule in ('none', 'bdry') or rule.startswith('split') or rule.startswith('pat') or rule == 'periodic' or not nb:
            continue
        for r in range(H):
            holders = [tvar(p, H + k) for p in nb for k, e in enumerate(edges) if r in e]
            clauses.append([-tvar(x, r)] + holders)
    pad = sys.argv[8] if len(sys.argv) > 8 else None      # e.g. '1h' = left row 1, right row h
    if pad:
        lr = 0 if pad[0] == '1' else H - 1
        rr = 0 if pad[1] == '1' else H - 1
        for x in range(L):
            clauses.append([tvar(x, lr)])
        for x in range(W - R, W):
            clauses.append([tvar(x, rr)])
    if rule == 'periodic':
        dl = sorted(dpos)
        classes = {}
        for p in dl:
            for j in range(g):
                x = p + 1 + j
                if x < W and x not in dpos:
                    classes.setdefault(j, []).append(x)
        for j, xs in classes.items():
            for x in xs:
                clauses.append([tvar(x, 0), tvar(x, H - 1)])
            for x, y in zip(xs, xs[1:]):
                clauses.append([-tvar(x, 0), tvar(y, 0)]); clauses.append([tvar(x, 0), -tvar(y, 0)])
    if rule.startswith('pat'):          # pat11h or pat1hh: fixed sea pattern after each double
        patt = rule[3:]
        dl = sorted(dpos)
        for p in dl:
            for j, ch in enumerate(patt):
                x = p + 1 + j
                if x < W and x not in dpos:
                    clauses.append([tvar(x, 0 if ch == '1' else H - 1)])
        for x in range(min(dl)):
            clauses.append([tvar(x, H - 1)])
    if rule.startswith('split'):
        frac = float(rule[5:]) if len(rule) > 5 else 0.5
        cut = int(W * frac)
        for x in range(W):
            if x not in dpos:
                clauses.append([tvar(x, 0)] if x < cut else [tvar(x, H - 1)])
    if rule == 'bdry':
        for x in range(W):
            if x not in dpos:
                clauses.append([tvar(x, 0), tvar(x, H - 1)])
    if rule == 'same':
        for x in range(W - 1):
            if x not in dpos and (x + 1) not in dpos and any(p < x for p in dpos):
                for r in range(H):
                    clauses.append([-tvar(x, r), tvar(x + 1, r)])
                    clauses.append([tvar(x, r), -tvar(x + 1, r)])
    status, model, dt = base.solve_capped('cadical153', clauses, cap)
    rec = {'pad': sys.argv[8] if len(sys.argv) > 8 else None, 'rule': rule, 'h': H, 'g': g, 'L': L, 'R': R, 'w': W, 'A': [a + 1 for a in A], 'status': status, 'solve_s': round(dt)}
    if model is not None:
        pts = {((v - 1) % W, (v - 1) // W) for v in model if 0 < v <= n}
        rec['valid'] = collision(rectangles(H, W), mask(pts, W)) is None
        rec['word'] = ','.join(''.join(str(y + 1) for y in range(H) if (x, y) in pts) for x in range(W))
    print(json.dumps(rec), flush=True)
    json.dump(rec, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), f'sp_h{H}_g{g}_L{L}_R{R}_p{sys.argv[5]}_{rule}{"_" + sys.argv[8] if len(sys.argv) > 8 else ""}.json'), 'w'))


if __name__ == '__main__':
    main()
