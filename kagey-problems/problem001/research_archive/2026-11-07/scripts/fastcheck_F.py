"""fastcheck.violations with an explicit pair set F (for blocks that are part of a larger board)."""
import numpy as np
from fastcheck import shapes, rival


def violations_F(h, cols, F, detail=False):
    m = len(cols)
    black = np.zeros((m, h + 2), dtype=bool)
    for x, c in enumerate(cols):
        for r in c:
            black[x, r] = True
    B = [frozenset(c) for c in cols]
    seen = {}; bad = 0; det = []
    for sh in shapes(h):
        span = max(dx for dx, _ in sh)
        for x0 in range(0, m - span):
            cs = [(x0 + dx, r) for dx, r in sh]
            k = [black[x, r] for x, r in cs]
            if sum(k) < 2:
                continue
            P = frozenset(c for c, kk in zip(cs, k) if not kk)
            v = None
            if not P:
                v = 'hidden'
            elif P in seen:
                v = 'tilt-tilt'
            else:
                seen[P] = cs
                if rival(P, B, F):
                    v = 'rival'
            if v:
                bad += 1
                if detail:
                    det.append((v, cs, sorted(P)))
    return (bad, det) if detail else bad


def parity_F(h):
    return {frozenset((a, b)) for a in range(1, h + 1) for b in range(a + 1, h + 1) if (b - a) % 2}
