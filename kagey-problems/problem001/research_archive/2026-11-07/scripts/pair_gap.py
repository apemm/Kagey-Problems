"""For alternating seas with two doubles at gap D, find for each D the number of ordered edge pairs
(from K_{odd,even}) that are valid. Usage: python pair_gap.py h Dmax"""
import sys
from fastcheck import violations


def main():
    h, Dmax = int(sys.argv[1]), int(sys.argv[2])
    E = [(a, b) for a in range(1, h + 1) for b in range(a + 1, h + 1) if (b - a) % 2]
    W = 1 + (h - 1) ** 2 // 4
    for D in range(1, Dmax + 1):
        ok = 0
        for e1 in E:
            for e2 in E:
                if e1 == e2:
                    continue
                cols = [{1}] * (W + 2) + [set(e1)] + [{h}] * (D - 1) + [set(e2)] + [{1}] * (W + 2)
                if violations(h, cols, stop=True) == 0:
                    ok += 1
        print('h', h, 'D', D, 'valid ordered edge pairs', ok, 'of', len(E) * (len(E) - 1), flush=True)


if __name__ == '__main__':
    main()
