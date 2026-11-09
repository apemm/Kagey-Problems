"""Classify the two-white-corner violations of random "1, x, h" boards.
Key: (violation type, black kinds, diagonal or side, white pair shape, kinds of white columns).
Usage: py v2classes.py h trials"""
import sys, random
from cegar_board import check
from v1laws import board


def main():
    h, T = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(2)
    tally = {}
    for _ in range(T):
        cols = board(h, rng)
        n, det = check(h, cols)
        for v, cs, Pw, partner in det:
            if len(Pw) != 2:
                continue
            Pw = sorted(Pw)
            blk = [c for c in cs if c not in set(Pw)]
            kind = lambda c: 'D' if c[0] % 4 == 0 else ('M' if c[0] % 4 == 2 else 'F')
            # corners in cyclic order: cs = (left, bottom-ish...) -> diagonal iff the two blacks are not adjacent
            (x1, y1), (x2, y2) = blk
            (w1, z1), (w2, z2) = Pw
            diag = (x1 + x2 == w1 + w2 and y1 + y2 == z1 + z2)
            shape = 'V' if w1 == w2 else ('H' if z1 == z2 else 'G')
            ks = ''.join(sorted(kind(c) for c in blk))
            wk = ''.join(sorted(kind(c) for c in Pw))
            if v == 'tilt-tilt':
                ob = [c for c in partner if c not in set(Pw)]
                pk = ''.join(sorted(kind(c) for c in ob))
                key = (v, ks, 'diag' if diag else 'side', shape, wk, 'partner ' + pk)
            else:
                key = (v, ks, 'diag' if diag else 'side', shape, wk)
            tally[key] = tally.get(key, 0) + 1
    for k in sorted(tally, key=lambda k: -tally[k]):
        print(tally[k], k)


if __name__ == '__main__':
    main()
