"""Is a single staircase L_g = {{a, a+g}} valid as an isolated block? Doubles at spacing s,
order ascending or descending in a, seas: left row L, right row R, inside row I (between doubles).
Usage: python stair_blocks.py h"""
import sys
from fastcheck import violations


def main():
    h = int(sys.argv[1])
    W = 1 + (h - 1) ** 2 // 4
    for g in range(1, h, 2):
        edges = [(a, a + g) for a in range(1, h - g + 1)]
        found = []
        for order in ('asc', 'desc'):
            es = edges if order == 'asc' else edges[::-1]
            for s in (2, 3, 4, 5, 6):
                for L, I, R in ((1, 1, 1), (h, h, h), (1, 1, h), (1, h, h), (h, 1, 1), (h, h, 1), (1, h, 1), (h, 1, h)):
                    cols = [{L}] * (W + 2)
                    for j, e in enumerate(es):
                        if j:
                            cols += [{I}] * (s - 1)
                        cols.append(set(e))
                    cols += [{R}] * (W + 2)
                    if violations(h, cols, stop=True) == 0:
                        found.append((order, s, L, I, R))
        print('h', h, 'g', g, 'blocks', len(edges), 'valid configs', found[:6], 'count', len(found), flush=True)


if __name__ == '__main__':
    main()
