"""Annealing over edge orders for alternating seas at uniform gap D (default 4).
Usage: python anneal_alt.py h steps seed [D]"""
import sys, random, math, json, time
from fastcheck import violations
from uniform_alt import board


def main():
    h, steps, seed = map(int, sys.argv[1:4]); D = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    rng = random.Random(seed)
    E = [(a, b) for a in range(1, h + 1) for b in range(a + 1, h + 1) if (b - a) % 2]
    M = 1 + (h - 1) ** 2 // 4 + 2
    order = E[:]; rng.shuffle(order)
    cur = violations(h, board(h, order, D, M)); best = cur; t0 = time.time()
    for s in range(steps):
        T = 1.5 * (1 - s / steps) + 0.05
        o2 = order[:]
        i, j = rng.sample(range(len(o2)), 2)
        if rng.random() < 0.5:
            o2[i], o2[j] = o2[j], o2[i]
        else:
            e = o2.pop(i); o2.insert(j, e)
        v = violations(h, board(h, o2, D, M))
        if v <= cur or rng.random() < math.exp((cur - v) / T):
            order, cur = o2, v
            if cur < best:
                best = cur; print('step', s, 'violations', cur, 'time', round(time.time() - t0), flush=True)
        if cur == 0:
            cols = board(h, order, D, M)
            word = ','.join(''.join(str(r) for r in sorted(c)) for c in cols)
            json.dump({'h': h, 'D': D, 'order': order, 'w': len(cols), 'word': word}, open('alt_h%d_D%d_s%d.json' % (h, D, seed), 'w'))
            print('FOUND', order, flush=True); return
    print('END best', best, flush=True)


if __name__ == '__main__':
    main()
