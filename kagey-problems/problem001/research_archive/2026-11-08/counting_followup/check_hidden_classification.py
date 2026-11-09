"""Exact independent checks for the hidden-rectangle classification."""
from collections import defaultdict
from itertools import combinations
from math import gcd
from pathlib import Path
import json


def rectangles(h, m):
    groups = defaultdict(list)
    pts = [(x, r) for x in range(m) for r in range(1, h + 1)]
    for a, b in combinations(pts, 2):
        groups[(a[0]+b[0], a[1]+b[1],
                (a[0]-b[0])**2 + (a[1]-b[1])**2)].append((a, b))
    out = set()
    for diagonals in groups.values():
        for d, e in combinations(diagonals, 2):
            r = frozenset(d + e)
            if len(r) == 4:
                out.add(r)
    return out


def minus(a, b):
    return a[0]-b[0], a[1]-b[1]


def plus(a, b):
    return a[0]+b[0], a[1]+b[1]


def axis(r):
    return len({p[0] for p in r}) == len({p[1] for p in r}) == 2


all_rects = rectangles(9, 10)
crossed = subdivided = unit = 0
for rect in all_rects:
    if axis(rect):
        continue
    diag = None
    for a, c in combinations(rect, 2):
        b, d = tuple(rect - {a, c})
        if plus(a, c) == plus(b, d) and a[0] != c[0] and a[1] != c[1]:
            diag = a, c, b, d
            break
    if diag:
        a, c, b, d = diag
        u, v = (a[0], c[1]), (c[0], a[1])
        first, second = frozenset((u, v, b, d)), frozenset((u, v, a, c))
        assert first in all_rects and second in all_rects and first != second
        assert first ^ second == rect
        crossed += 1
        continue
    cx = sum(p[0] for p in rect)//4
    cy = sum(p[1] for p in rect)//4
    size = max(abs(p[0]-cx) for p in rect)
    assert rect == frozenset(((cx-size,cy),(cx+size,cy),(cx,cy-size),(cx,cy+size)))
    if size == 1:
        unit += 1
        continue
    p = (cx-size,cy)
    v, w = (size,-size), (size,size)
    divisor = gcd(abs(w[0]), abs(w[1]))
    w0 = w[0]//divisor, w[1]//divisor
    mid, mid2 = plus(p,w0), plus(plus(p,v),w0)
    first = frozenset((p,plus(p,v),mid,mid2))
    second = frozenset((plus(p,w),plus(plus(p,v),w),mid,mid2))
    assert first in all_rects and second in all_rects and first != second
    assert first ^ second == rect
    subdivided += 1

black = {(0,2),(1,1),(1,3),(2,2),(3,2),(3,3)}
small_rects = rectangles(3,4)
presentations = [rect - black for rect in small_rects]
assert len(set(presentations)) == len(presentations)
assert presentations.count(frozenset()) == 1
output = {"grid": [9,10], "rectangles": len(all_rects),
          "crossing_checks": crossed, "subdivision_checks": subdivided,
          "remaining_unit_diamonds": unit,
          "nonparity_example": {"grid": [3,4], "rectangles": len(small_rects),
                                 "valid": True, "hidden": 1, "black": len(black)}}
Path(__file__).with_name('hidden_classification_checks.json').write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps(output,indent=2))
