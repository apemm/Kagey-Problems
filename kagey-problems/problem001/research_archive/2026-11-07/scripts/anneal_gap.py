"""Spacing-4 boards in the '1, x, h' family: each double has row h just before it and row 1 just after
it; the middle cell x of each gap is free (1 or h). Margins: one row-h cell before the first double, one
row-1 cell after the last. Anneal over the order and the middle cells. Usage: python anneal_gap.py h steps seed"""
import sys, random, math, json, time
from fastcheck import violations


def build(h, order, mids):
    cols = [{h}]
    for k, e in enumerate(order):
        if k:
            cols += [{1}, {mids[k - 1]}, {h}]
        cols.append(set(e))
    return cols + [{1}]


def main():
    h, steps, seed = map(int, sys.argv[1:4]); rng = random.Random(seed)
    E = [(a, b) for a in range(1, h + 1) for b in range(a + 1, h + 1) if (b - a) % 2]
    order = E[:]; rng.shuffle(order); mids = [rng.choice((1, h)) for _ in range(len(E) - 1)]
    cur = violations(h, build(h, order, mids)); best = cur; t0 = time.time()
    for s in range(steps):
        T = 1.2 * (1 - s / steps) + 0.05
        o2, m2 = order[:], mids[:]
        rr = rng.random()
        if rr < 0.4:
            i, j = rng.sample(range(len(o2)), 2); o2[i], o2[j] = o2[j], o2[i]
        elif rr < 0.8:
            i, j = rng.sample(range(len(o2)), 2); e = o2.pop(i); o2.insert(j, e)
        else:
            k = rng.randrange(len(m2)); m2[k] = h if m2[k] == 1 else 1
        v = violations(h, build(h, o2, m2))
        if v <= cur or rng.random() < math.exp((cur - v) / T):
            order, mids, cur = o2, m2, v
            if cur < best:
                best = cur; print('step', s, 'violations', cur, 'time', round(time.time() - t0), flush=True)
        if cur == 0:
            cols = build(h, order, mids)
            word = ','.join(''.join(str(r) for r in sorted(c)) for c in cols)
            json.dump({'h': h, 'w': len(cols), 'word': word, 'order': order, 'mids': mids}, open('gap_h%d_s%d.json' % (h, seed), 'w'))
            print('FOUND width', len(cols), 'order', order, 'mids', mids, flush=True); return
    print('END best', best, flush=True)


if __name__ == '__main__':
    main()
