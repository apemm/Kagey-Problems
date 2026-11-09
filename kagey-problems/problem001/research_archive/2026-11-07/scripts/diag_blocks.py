"""Diagonal-staircase blocks: K_{odd,even} = disjoint union of L_d = {{a, a+d}} for odd d.
Each block lays out its edges in order of a (inc or dec), consecutive doubles separated by s-1 sea
columns; blocks separated by G sea columns; sea rows from a rule. Check with fastcheck.
Usage: python diag_blocks.py h"""
import sys, itertools
from fastcheck import violations


def build(h, s, G, dirs, sea, block_order, pad):
    W = 1 + (h - 1) ** 2 // 4
    ds = list(range(1, h, 2))
    ds = [ds[i] for i in block_order]
    cols = []
    def seacol(i):
        if sea == 'one':
            return {1}
        if sea == 'h':
            return {h}
        if sea == 'alt':
            return {1} if i % 2 == 0 else {h}
        return {1}
    k = 0
    cols += [{1}] * pad
    for bi, d in enumerate(ds):
        aa = list(range(1, h - d + 1))
        if dirs[bi] == 'dec':
            aa = aa[::-1]
        for j, a in enumerate(aa):
            cols.append({a, a + d})
            if j < len(aa) - 1:
                for _ in range(s - 1):
                    cols.append(seacol(k)); k += 1
        if bi < len(ds) - 1:
            for _ in range(G):
                cols.append(seacol(k)); k += 1
    cols += [{1}] * pad
    return cols


def main():
    h = int(sys.argv[1])
    nb = len(range(1, h, 2))
    best = None
    for s in (1, 2, 3, 4):
        for G in (1, 2, 3, 4, 6):
            for sea in ('one', 'alt', 'h'):
                for dirs in itertools.product(('inc', 'dec'), repeat=nb):
                    for bo in itertools.permutations(range(nb)):
                        cols = build(h, s, G, dirs, sea, bo, 1)
                        v = violations(h, cols, stop=False)
                        if best is None or v < best[0]:
                            best = (v, s, G, sea, dirs, bo, len(cols))
                        if v == 0:
                            print('VALID', h, 's', s, 'G', G, sea, dirs, bo, 'width', len(cols), flush=True)
    print('best', best, flush=True)


if __name__ == '__main__':
    main()
