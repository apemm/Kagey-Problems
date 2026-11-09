"""Spacing-4 boards with one switch: row-1 sea up to the switch slot, row-h sea after it, margins in
the matching rows. Anneal over the edge order and the switch slot. Usage: python anneal_split.py h steps seed"""
import sys, random, math, json, time
from fastcheck import violations


def build(h, order, k0, M):
    cols = [{1}] * M
    for k, e in enumerate(order):
        if k:
            cols += [{1 if k <= k0 else h}] * 3
        cols.append(set(e))
    return cols + [{h}] * M


def main():
    h, steps, seed = map(int, sys.argv[1:4])
    rng = random.Random(seed)
    E = [(a, b) for a in range(1, h + 1) for b in range(a + 1, h + 1) if (b - a) % 2]
    E.sort(key=lambda e: e[0] + e[1])
    M = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    order = E[:]; k0 = len(E) // 2
    cur = violations(h, build(h, order, k0, M)); best = cur; t0 = time.time()
    for s in range(steps):
        T = 1.5 * (1 - s / steps) + 0.05
        o2, k2 = order[:], k0
        rr = rng.random()
        if rr < 0.45:
            i, j = rng.sample(range(len(o2)), 2); o2[i], o2[j] = o2[j], o2[i]
        elif rr < 0.9:
            i, j = rng.sample(range(len(o2)), 2); e = o2.pop(i); o2.insert(j, e)
        else:
            k2 = max(0, min(len(o2) - 1, k0 + rng.choice((-1, 1))))
        v = violations(h, build(h, o2, k2, M))
        if v <= cur or rng.random() < math.exp((cur - v) / T):
            order, k0, cur = o2, k2, v
            if cur < best:
                best = cur; print('step', s, 'violations', cur, 'switch', k0, 'time', round(time.time() - t0), flush=True)
        if cur == 0:
            cols = build(h, order, k0, M)
            word = ','.join(''.join(str(r) for r in sorted(c)) for c in cols)
            json.dump({'h': h, 'w': len(cols), 'word': word, 'order': order, 'switch': k0}, open('split_h%d_s%d.json' % (h, seed), 'w'))
            print('FOUND width', len(cols), 'order', order, 'switch', k0, flush=True); return
    print('END best', best, flush=True)


if __name__ == '__main__':
    main()
