import os
"""Fast validity checker for blackouts whose columns are singletons or doubles with distinct pairs
forming a triangle-free graph (so axis-aligned rectangles are automatically fine). Counts violations:
hidden tilted rectangles, tilted presentations with an axis-aligned rival (Lemma 'rival'), and pairs of
tilted rectangles with the same presentation. Rows are 1..h, columns 0..m-1.
"""
import numpy as np
from math import isqrt
from functools import lru_cache


@lru_cache(None)
def shapes(h):
    """Tilted rectangle shapes as arrays of (dx, row) for the 4 corners, leftmost column dx=0."""
    W = 1 + (h - 1) ** 2 // 4
    out = []
    # leftmost corner (0, r); sides (a,-b) and (c,d), a,b,c,d >= 1, ac = bd; corners
    # (0,r), (a, r-b), (c, r+d), (a+c, r-b+d)
    for b in range(1, h):
        for d in range(1, h - b):
            for a in range(1, b * d + 1):
                if (b * d) % a:
                    continue
                c = b * d // a
                if a + c > W:
                    continue
                for r in range(1 + b, h - d + 1):
                    out.append(((0, r), (a, r - b), (c, r + d), (a + c, r - b + d)))
    return out


def violations(h, cols, stop=False, detail=False):
    """cols: list of sets of rows. Returns the number of violations (or the first if stop)."""
    m = len(cols)
    black = np.zeros((m, h + 2), dtype=bool)
    for x, c in enumerate(cols):
        for r in c:
            black[x, r] = True
    F = set()
    for c in cols:
        if len(c) == 2:
            F.add(frozenset(c))
    B = [frozenset(c) for c in cols]
    seen = {}
    bad = 0
    det = []
    for sh in shapes(h):
        span = max(dx for dx, _ in sh)
        for x0 in range(0, m - span):
            cs = [(x0 + dx, r) for dx, r in sh]
            k = [black[x, r] for x, r in cs]
            nb = sum(k)
            if nb < 2:
                continue
            P = frozenset(c for c, kk in zip(cs, k) if not kk)
            v = None
            if not P:
                v = 'hidden'
            else:
                if P in seen:
                    v = 'tilt-tilt'
                else:
                    seen[P] = cs
                    if rival(P, B, F):
                        v = 'rival'
            if v:
                bad += 1
                if detail:
                    det.append((v, cs, sorted(P)))
                if stop:
                    return (bad, det) if detail else bad
    return (bad, det) if detail else bad


def rival(P, B, F):
    P = sorted(P)
    if len(P) == 1:
        (x, r), = P
        return any(frozenset((r, s)) in F for s in B[x] if s != r)
    (x, r), (z, s) = P
    if x == z:
        return frozenset((r, s)) in F
    if r == s:
        return bool(B[x] & B[z])
    return (s in B[x]) and (r in B[z])


if __name__ == '__main__':
    import sys, json
    sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..')))
    from verify_narrow import rectangles, mask, collision
    # cross-check against verify_narrow on stored witnesses
    for f, h in [('sp_h6_g2_L1_R1_p135.json', 6), ('sp_h7_g2_L1_R1_p246.json', 7)]:
        w = json.load(open(f))['word'].split(',')
        cols = [set(int(c) for c in s) for s in w]
        print(f, violations(h, cols), collision(rectangles(h, len(w)), mask([(x, r - 1) for x, c in enumerate(cols) for r in c], len(w))) is None)
    # a known invalid one: row-1 sea with lone double {2,5} on 5 rows
    cols = [{1}] * 8 + [{2, 5}] + [{1}] * 8
    print('lone 25 in row-1 sea (invalid):', violations(5, cols))
