"""Independent rectangle enumeration and blackout check.

A rectangle is a pair of distinct lattice segments (its diagonals) with the same
midpoint and the same length. The check below enumerates every such pair in an
h x m grid, with no use of any solver encoding or shape table.

A board is a list of columns; each column is a list of black rows, numbered from 1.
The presentation of a rectangle is its set of white corners. A board is a blackout
exactly when distinct rectangles have distinct presentations. Three corners
determine a rectangle, so a clash needs two rectangles with at most two white
corners each; an all-black rectangle is reported separately as hidden.
"""
from collections import defaultdict
import numpy as np


def check_board(h, cols, want_rectangles=False):
    """Complete check by the diagonal method, in chunks of constant x1+x2."""
    m = len(cols)
    B = np.zeros((m, h), dtype=np.int8)
    for x, c in enumerate(cols):
        for r in c:
            B[x, r - 1] = 1
    N = m * h
    ys = np.arange(h)
    y1g, y2g = np.meshgrid(ys, ys, indexing='ij')
    y1g = y1g.ravel(); y2g = y2g.ravel()
    total = 0; hidden = 0; weak = 0
    keys = []
    for sx in range(0, 2 * (m - 1) + 1):
        lo = max(0, sx - (m - 1)); hi = sx // 2
        x1 = np.arange(lo, hi + 1)
        X1 = np.repeat(x1, h * h); X2 = sx - X1
        Y1 = np.tile(y1g, len(x1)); Y2 = np.tile(y2g, len(x1))
        keep = (X1 < X2) | ((X1 == X2) & (Y1 < Y2))
        X1 = X1[keep]; X2 = X2[keep]; Y1 = Y1[keep]; Y2 = Y2[keep]
        L = (X2 - X1) ** 2 + (Y2 - Y1) ** 2
        key = (Y1 + Y2).astype(np.int64) * (4 * (m * m + h * h)) + L
        order = np.argsort(key, kind='stable')
        key = key[order]; X1 = X1[order]; X2 = X2[order]; Y1 = Y1[order]; Y2 = Y2[order]
        b1 = B[X1, Y1]; b2 = B[X2, Y2]
        i1 = X1 * h + Y1; i2 = X2 * h + Y2
        n = len(key); k = 1
        while k < n:
            same = key[:-k] == key[k:]
            if not same.any():
                break
            a = np.nonzero(same)[0]; b = a + k
            total += len(a)
            cnt = b1[a] + b2[a] + b1[b] + b2[b]
            sel = cnt >= 2
            if sel.any():
                a = a[sel]; b = b[sel]
                ids = np.stack([i1[a], i2[a], i1[b], i2[b]], axis=1)
                blk = np.stack([b1[a], b2[a], b1[b], b2[b]], axis=1)
                white = np.where(blk == 1, -1, ids)
                white.sort(axis=1)
                nwhite = (white >= 0).sum(axis=1)
                hidden += int((nwhite == 0).sum())
                w = white[nwhite > 0]
                weak += len(w)
                keys.append((w[:, 2] + 1).astype(np.int64) * (N + 1) + (w[:, 3] + 1))
            k += 1
    allk = np.concatenate(keys) if keys else np.zeros(0, dtype=np.int64)
    distinct = len(np.unique(allk))
    out = {'height': h, 'width': m, 'black': int(B.sum()), 'rectangles': int(total),
           'rectangles_with_two_or_more_black_corners': int(weak + hidden),
           'hidden_rectangles': int(hidden),
           'distinct_presentations_among_them': int(distinct),
           'valid': bool(hidden == 0 and distinct == weak)}
    return out


def check_board_plain(h, cols):
    """Slow reference version in plain Python, for small boards. Compares every presentation."""
    m = len(cols)
    black = {(x, r - 1) for x, c in enumerate(cols) for r in c}
    pts = [(x, y) for x in range(m) for y in range(h)]
    groups = defaultdict(list)
    for i, p in enumerate(pts):
        for q in pts[i + 1:]:
            groups[(p[0] + q[0], p[1] + q[1], (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)].append((p, q))
    seen = {}; total = 0
    for g in groups.values():
        for i, d in enumerate(g):
            for e in g[i + 1:]:
                total += 1
                pres = frozenset(c for c in d + e if c not in black)
                if pres in seen:
                    return {'rectangles': total, 'valid': False, 'clash': [sorted(pres)]}
                seen[pres] = 1
    return {'rectangles': total, 'valid': True}


def count_rectangles_by_sides(h, m):
    """Independent count from perpendicular side vectors, used as a cross-check."""
    from math import gcd
    n = (h * (h - 1) // 2) * (m * (m - 1) // 2)
    for p in range(1, max(h, m)):
        for q in range(1, max(h, m)):
            if gcd(p, q) != 1:
                continue
            s = 1
            while s * q <= h - 1 and s * p <= m - 1:
                t = 1
                while s * q + t * p <= h - 1 and s * p + t * q <= m - 1:
                    n += (h - s * q - t * p) * (m - s * p - t * q)
                    t += 1
                s += 1
    return n


def parse_word(word):
    return [[int(ch) for ch in tok] for tok in word.split(',')]
