"""Simulated annealing for spacing-4 boundary-sea boards: doubles (all edges of K_{odd,even}) in columns
M, M+4, ..., sea columns in row 1 or row h, margins of M columns on each side.
Moves: swap two edges, flip one sea column. Objective: number of violations (fastcheck).
Usage: python anneal4.py h steps seed [margin]"""
import sys, random, math, json, time
from fastcheck import violations


def build(h, order, seas, M, sp=4):
    cols = []
    it = iter(seas)
    width = 2 * M + sp * (len(order) - 1) + 1
    dpos = {M + sp * k: k for k in range(len(order))}
    for x in range(width):
        if x in dpos:
            cols.append(set(order[dpos[x]]))
        else:
            cols.append({next(it)})
    return cols


def main():
    h, steps, seed = map(int, sys.argv[1:4])
    M = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    rng = random.Random(seed)
    E = [(a, b) for a in range(1, h + 1) for b in range(a + 1, h + 1) if (b - a) % 2]
    order = E[:]
    rng.shuffle(order)
    nsea = 2 * M + 4 * (len(E) - 1) + 1 - len(E)
    half = nsea // 2
    seas = [1] * half + [h] * (nsea - half)
    cur = violations(h, build(h, order, seas, M))
    best = cur
    T0 = 2.0
    t0 = time.time()
    for s in range(steps):
        T = T0 * (1 - s / steps) + 0.05
        o2, s2 = order[:], seas[:]
        if rng.random() < 0.6:
            i, j = rng.sample(range(len(o2)), 2)
            o2[i], o2[j] = o2[j], o2[i]
        else:
            k = rng.randrange(len(s2))
            s2[k] = h if s2[k] == 1 else 1
        v = violations(h, build(h, o2, s2, M))
        if v <= cur or rng.random() < math.exp((cur - v) / T):
            order, seas, cur = o2, s2, v
            if cur < best:
                best = cur
                print('step', s, 'violations', cur, 'time', round(time.time() - t0), flush=True)
        if cur == 0:
            cols = build(h, order, seas, M)
            word = ','.join(''.join(str(r) for r in sorted(c)) for c in cols)
            json.dump({'h': h, 'w': len(cols), 'word': word, 'valid': True}, open('anneal4_h%d_s%d.json' % (h, seed), 'w'))
            print('FOUND width', len(cols), word, flush=True)
            return
    print('END best', best, flush=True)


if __name__ == '__main__':
    main()
