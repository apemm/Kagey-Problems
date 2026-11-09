"""Fix the doubles by a rule (edge order, spacing g), let SAT choose the sea rows.
Usage: python fixed_sat.py H g ORDER CAP [L R]. A = odd rows, B = even rows.
ORDER: starB (by b then a), starA (by a then b), sum (a+b, then a), diff (b-a signed, then a),
absdiff (|b-a| then a), sumrev, starBrev."""
import sys, os, json, time
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')))
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'jis', 'scripts')))
import six_row_structured_sat as base
from verify_narrow import collision, mask, rectangles


def order(H, rule):
    A = [r for r in range(H) if r % 2 == 0]      # zero-based: rows 1,3,5,... one-based
    B = [r for r in range(H) if r % 2 == 1]
    E = [(a, b) for a in A for b in B]
    if rule.startswith('diag'):
        # diag<dirs> e.g. diagIDI: blocks d = 1,3,5,... in ascending d; I = a increasing, D = decreasing
        dirs = rule[4:]
        out = []
        for i, d in enumerate(range(1, H, 2)):
            aa = list(range(0, H - d))
            if i < len(dirs) and dirs[i] == 'D':
                aa = aa[::-1]
            out += [(a, a + d) for a in aa]
        return A, B, out
    if rule.startswith('rdiag'):
        dirs = rule[5:]
        out = []
        for i, d in enumerate(list(range(1, H, 2))[::-1]):
            aa = list(range(0, H - d))
            if i < len(dirs) and dirs[i] == 'D':
                aa = aa[::-1]
            out += [(a, a + d) for a in aa]
        return A, B, out
    key = {'starB': lambda e: (e[1], e[0]), 'starA': lambda e: (e[0], e[1]),
           'sum': lambda e: (e[0] + e[1], e[0]), 'sumrev': lambda e: (e[0] + e[1], -e[0]),
           'diff': lambda e: (e[1] - e[0], e[0]), 'absdiff': lambda e: (abs(e[1] - e[0]), e[0]),
           'starBrev': lambda e: (e[1], -e[0]),
           'len': lambda e: (abs(e[1] - e[0]), e[0]), 'lenrev': lambda e: (abs(e[1] - e[0]), -min(e)),
           'lenalt': lambda e: (abs(e[1] - e[0]), (-1) ** (abs(e[1] - e[0]) // 2) * min(e))}[rule]
    return A, B, sorted(E, key=key)


def main():
    H, g, rule, cap = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4])
    L = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    R = int(sys.argv[6]) if len(sys.argv) > 6 else 1
    base.ROWS = H; base.COLLAR = 1 + (H - 1) ** 2 // 4
    A, B, E = order(H, rule)
    q = len(E)
    W = L + q + (q - 1) * g + R
    clauses, n, info, _ = base.encode_a(W, (tuple(A), tuple(B)))
    edges = [(min(a, b), max(a, b)) for a in A for b in B]      # encode_a type order
    ntypes = H + q
    tvar = lambda x, j: n + x * ntypes + j + 1
    dcols = {}
    for k, (a, b) in enumerate(E):
        x = L + k * (g + 1)
        dcols[x] = (min(a, b), max(a, b))
        clauses.append([tvar(x, H + edges.index((min(a, b), max(a, b))))])
    bd = len(sys.argv) > 7 and sys.argv[7] == 'bdry'
    for x in range(W):
        if x not in dcols:
            clauses.append([tvar(x, 0), tvar(x, H - 1)] if bd else [tvar(x, j) for j in range(H)])
    status, model, dt = base.solve_capped('cadical153', clauses, cap)
    rec = {'bdry': bd, 'h': H, 'g': g, 'rule': rule, 'w': W, 'status': status, 'solve_s': round(dt)}
    if model is not None:
        pts = {((v - 1) % W, (v - 1) // W) for v in model if 0 < v <= n}
        rec['valid'] = collision(rectangles(H, W), mask(pts, W)) is None
        rec['word'] = ','.join(''.join(str(y + 1) for y in range(H) if (x, y) in pts) for x in range(W))
    print(json.dumps(rec), flush=True)
    json.dump(rec, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), f'fx_h{H}_g{g}_{rule}_{"bdry" if bd else "free"}.json'), 'w'))


if __name__ == '__main__':
    main()
