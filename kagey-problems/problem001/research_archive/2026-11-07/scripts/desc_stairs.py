"""Descending diagonal staircases L_g (a decreasing), all blocks contiguous at spacing 4 (three row-1 sea
columns after every double), W_h row-1 padding at both ends. Report violations by type."""
import sys
from collections import Counter
from fastcheck import violations
def board(h, order, sea=1):
    W = 1 + (h-1)**2//4
    cols = [{sea}]*W; pos = {}
    edges = []
    for g in order:
        for a in range(h-g, 0, -1):
            edges.append((a, a+g))
    for i, e in enumerate(edges):
        pos[len(cols)] = e; cols.append(set(e))
        cols += [{sea}]*3
    cols += [{sea}]*(W-3)
    return cols, pos
def main():
  for h in range(6, int(sys.argv[1]) + 1):
    for name, order in (('asc g', list(range(1, h, 2))), ('desc g', list(range(1, h, 2))[::-1])):
        cols, pos = board(h, order)
        n, det = violations(h, cols, detail=True)
        kinds = Counter(k for k, _, _ in det)
        print(h, name, 'width', len(cols), 'violations', n, dict(kinds), flush=True)


if __name__ == '__main__':
    main()
