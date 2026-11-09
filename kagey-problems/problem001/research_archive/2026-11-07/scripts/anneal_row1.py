"""Annealing over edge orders in a pure row-1 sea with doubles every 4th column; objective counts
violations whose corners all lie inside the run of doubles. Usage: python anneal_row1.py h steps seed"""
import sys, random, math, json, time
from fastcheck import violations


def build(h, order, M):
    cols = [{1}] * M
    for k, e in enumerate(order):
        if k:
            cols += [{1}] * 3
        cols.append(set(e))
    return cols + [{1}] * M


def inner(h, order, M):
    cols = build(h, order, M)
    lo, hi = M, M + 4 * (len(order) - 1)
    v, det = violations(h, cols, detail=True)
    return sum(1 for k, cs, P in det if all(lo <= x <= hi for x, _ in cs))


def main():
    h, steps, seed = map(int, sys.argv[1:4])
    rng = random.Random(seed)
    E = [(a, b) for a in range(1, h + 1) for b in range(a + 1, h + 1) if (b - a) % 2]
    M = 1 + (h - 1) ** 2 // 4 + 2
    order = E[:]; rng.shuffle(order)
    cur = inner(h, order, M); best = cur; t0 = time.time()
    for s in range(steps):
        T = 1.5 * (1 - s / steps) + 0.05
        o2 = order[:]
        i, j = rng.sample(range(len(o2)), 2)
        if rng.random() < 0.5:
            o2[i], o2[j] = o2[j], o2[i]
        else:
            e = o2.pop(i); o2.insert(j, e)
        v = inner(h, o2, M)
        if v <= cur or rng.random() < math.exp((cur - v) / T):
            order, cur = o2, v
            if cur < best:
                best = cur; print('step', s, 'inner violations', cur, 'time', round(time.time() - t0), flush=True)
        if cur == 0:
            json.dump({'h': h, 'order': order}, open('row1_inner_h%d_s%d.json' % (h, seed), 'w'))
            print('FOUND', order, flush=True); return
    print('END best', best, flush=True)


if __name__ == '__main__':
    main()
