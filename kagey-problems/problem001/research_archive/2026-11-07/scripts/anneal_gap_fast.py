"""Faster annealing for the '1, x, h' spacing-4 family: moves are local (swap two slots at most 8 apart,
or flip one middle cell), and the change in the violation count is computed exactly on the column window
[min changed - 2W, max changed + W] (any violation touching a changed column has its leftmost corner
there, and two rectangles with one presentation lie within 2W of each other).
Usage: python anneal_gap_fast.py h steps seed"""
import sys, random, math, json, time
import numpy as np
from fastcheck import shapes, rival, violations
from anneal_gap import build


def count_range(h, cols, black, B, F, xlo, xhi):
    m = len(cols)
    seen = {}
    bad = 0
    for sh in shapes(h):
        span = max(dx for dx, _ in sh)
        for x0 in range(max(0, xlo), min(m - span, xhi + 1)):
            cs = [(x0 + dx, r) for dx, r in sh]
            k = [black[x, r] for x, r in cs]
            if sum(k) < 2:
                continue
            P = frozenset(c for c, kk in zip(cs, k) if not kk)
            if not P:
                bad += 1
            elif P in seen:
                bad += 1
            else:
                seen[P] = 1
                if rival(P, B, F):
                    bad += 1
    return bad


def arrays(h, cols):
    black = np.zeros((len(cols), h + 2), dtype=bool)
    for x, c in enumerate(cols):
        for r in c:
            black[x, r] = True
    return black, [frozenset(c) for c in cols]


def main():
    h, steps, seed = map(int, sys.argv[1:4]); rng = random.Random(seed)
    E = [(a, b) for a in range(1, h + 1) for b in range(a + 1, h + 1) if (b - a) % 2]
    F = {frozenset(e) for e in E}
    W = 1 + (h - 1) ** 2 // 4
    order = E[:]; rng.shuffle(order); mids = [rng.choice((1, h)) for _ in range(len(E) - 1)]
    cols = build(h, order, mids); black, B = arrays(h, cols)
    cur = violations(h, cols); best = cur; t0 = time.time()
    q = len(E)
    for s in range(steps):
        T = 1.0 * (1 - s / steps) + 0.03
        o2, m2 = order[:], mids[:]
        if rng.random() < 0.6:
            i = rng.randrange(q); j = min(q - 1, max(0, i + rng.choice([-8, -6, -4, -3, -2, -1, 1, 2, 3, 4, 6, 8])))
            if i == j:
                continue
            o2[i], o2[j] = o2[j], o2[i]
            xs = [1 + 4 * i, 1 + 4 * j]
        else:
            k = rng.randrange(q - 1); m2[k] = h if m2[k] == 1 else 1
            xs = [1 + 4 * k + 2]
        lo, hi = min(xs) - 2 * W, max(xs) + W
        before = count_range(h, cols, black, B, F, lo, hi)
        cols2 = build(h, o2, m2); black2, B2 = arrays(h, cols2)
        after = count_range(h, cols2, black2, B2, F, lo, hi)
        v = cur + after - before
        if v <= cur or rng.random() < math.exp((cur - v) / T):
            order, mids, cur, cols, black, B = o2, m2, v, cols2, black2, B2
            if cur < best:
                best = cur; print('step', s, 'violations', cur, 'time', round(time.time() - t0), flush=True)
                json.dump({'h': h, 'best': best, 'order': order, 'mids': mids}, open('gapbest_h%d_s%d.json' % (h, seed), 'w'))
        if cur == 0:
            real = violations(h, cols)
            print('full recheck', real, flush=True)
            if real == 0:
                word = ','.join(''.join(str(r) for r in sorted(c)) for c in cols)
                json.dump({'h': h, 'w': len(cols), 'word': word, 'order': order, 'mids': mids}, open('gapfast_h%d_s%d.json' % (h, seed), 'w'))
                print('FOUND width', len(cols), 'order', order, 'mids', mids, flush=True); return
            cur = real
    print('END best', best, 'final full', violations(h, cols), flush=True)


if __name__ == '__main__':
    main()
