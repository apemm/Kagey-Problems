"""Given an interior-valid order in a row-1 sea at spacing 4, anneal only the sea cells within W_h of
the ends (rows 1 or h; margins of W_h + 2) to remove all violations.
Usage: python endcaps.py h order_json steps seed"""
import sys, json, random, math
from fastcheck import violations


def main():
    h = int(sys.argv[1]); order = [tuple(e) for e in json.load(open(sys.argv[2]))['order']]
    steps, seed = int(sys.argv[3]), int(sys.argv[4]); rng = random.Random(seed)
    W = 1 + (h - 1) ** 2 // 4; M = W + 2
    cols = [{1}] * M
    for k, e in enumerate(order):
        if k:
            cols += [{1}] * 3
        cols.append(set(e))
    cols += [{1}] * M
    cols = [set(c) for c in cols]
    lo, hi = M, len(cols) - 1 - M
    free = [x for x in range(len(cols)) if len(cols[x]) == 1 and (x < lo + 2 * W or x > hi - 2 * W)]
    # start: margins in row h
    for x in free:
        if x < lo or x > hi:
            cols[x] = {h}
    cur = violations(h, cols); best = cur
    for s in range(steps):
        T = 1.0 * (1 - s / steps) + 0.05
        x = rng.choice(free); old = cols[x]
        cols[x] = {h} if old == {1} else {1}
        v = violations(h, cols)
        if v <= cur or rng.random() < math.exp((cur - v) / T):
            cur = v
            if cur < best:
                best = cur; print('step', s, 'violations', cur, flush=True)
        else:
            cols[x] = old
        if cur == 0:
            word = ','.join(''.join(str(r) for r in sorted(c)) for c in cols)
            json.dump({'h': h, 'w': len(cols), 'word': word}, open('endcap_h%d_s%d.json' % (h, seed), 'w'))
            print('FOUND width', len(cols), 'size', sum(len(c) for c in cols), word, flush=True); return
    print('END best', best, flush=True)


if __name__ == '__main__':
    main()
