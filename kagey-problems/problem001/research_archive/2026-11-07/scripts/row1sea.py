"""Which edges can live in a row-1 sea with doubles every 4 columns? Random orders, record the doubles
involved in each violation. Usage: python row1sea.py h trials [exclude_rows]"""
import sys, random
from collections import Counter
from fastcheck import violations


def board(h, order, g=3, pad=None):
    W = 1 + (h - 1) ** 2 // 4
    pad = W if pad is None else pad
    cols = [{1}] * pad
    pos = {}
    for i, e in enumerate(order):
        pos[len(cols)] = e
        cols.append(set(e))
        cols += [{1}] * g
    cols += [{1}] * (pad - g)
    return cols, pos


def main():
    h = int(sys.argv[1]); trials = int(sys.argv[2])
    excl = {int(c) for c in sys.argv[3].split(',')} if len(sys.argv) > 3 else set()
    A = [r for r in range(1, h + 1) if r % 2]; B = [r for r in range(1, h + 1) if r % 2 == 0]
    E = [(a, b) for a in A for b in B if a not in excl and b not in excl]
    blame = Counter(); total = Counter(); zero = 0
    rng = random.Random(1)
    for t in range(trials):
        order = E[:]; rng.shuffle(order)
        cols, pos = board(h, order)
        n, det = violations(h, cols, detail=True)
        if n == 0:
            zero += 1
        for e in order:
            total[e] += 1
        for kind, cs, P in det:
            xs = {x for x, _ in cs} | {x for x, _ in P}
            inv = {pos[x] for x in xs if x in pos}
            for e in inv:
                blame[(kind, e)] += 1
    print('h', h, 'edges', len(E), 'zero-violation orders', zero, '/', trials)
    per = Counter()
    for (k, e), c in blame.items():
        per[e] += c
    for e in sorted(E, key=lambda e: -per[e]):
        print(e, per[e], {k: c for (k, ee), c in blame.items() if ee == e})


if __name__ == '__main__':
    main()
