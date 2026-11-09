"""Verify the explicit axis-only staircase constructions, not optimality."""

from itertools import combinations
from collections import Counter
from math import isqrt


def construction(h, loss):
    n = h-3
    a = n//2
    left = list(range(3, 3+a))
    right = list(range(3+a, h))
    k = (isqrt(4*loss+1)-1)//2
    chosen_left, chosen_right = set(left[:k]), set(right[:k])
    triples = [(0, 1, 2)] + [(0, left[i], right[i]) for i in range(k)]
    doubles = [(1, x) for x in left[k:]] + [(2, y) for y in right[k:]]
    doubles += [(x, y) for x in left for y in right
                if not (x in chosen_left and y in chosen_right)]
    remove = loss-k*(k+1)
    return triples + doubles[remove:]


def verify(h, loss):
    cols = construction(h, loss)
    owners = {}
    for i, rows in enumerate(cols):
        for pair in combinations(sorted(rows), 2):
            assert pair not in owners, (h, loss, "four-cycle", pair)
            owners[pair] = i
    for a, b, c in combinations(range(h), 3):
        ids = [owners.get((a,b)), owners.get((a,c)), owners.get((b,c))]
        assert None in ids or len(set(ids)) != 3, (h, loss, "six-cycle", a,b,c)
    w = h*h//4-h//2
    k = (isqrt(4*loss+1)-1)//2
    assert len(cols) == w-loss
    assert sum(map(len, cols)) == 2*(w-loss)+k+1


cases = 0
for height in (15, 27, 39, 51, 63, 75):
    for loss in range((height-3)//12):
        verify(height, loss)
        cases += 1
print(f"PASS: {cases} staircase constructions have no axis four-/six-cycle")

# Check the description multiplicity at the first height of Section 5.
h = 9
descriptions = Counter()
for triple in combinations(range(h), 3):
    outside = sorted(set(range(h))-set(triple))
    for left_tuple in combinations(outside, 3):
        right_tuple = tuple(x for x in outside if x not in left_tuple)
        if left_tuple > right_tuple:
            continue
        for center in triple:
            other = [x for x in triple if x != center]
            for first, second in (other, other[::-1]):
                for u in left_tuple:
                    for v in right_tuple:
                        cols = [triple, (center,u,v)]
                        cols += [(first,x) for x in left_tuple if x != u]
                        cols += [(second,y) for y in right_tuple if y != v]
                        cols += [(x,y) for x in left_tuple for y in right_tuple
                                 if (x,y) != (u,v)]
                        key = tuple(sorted(tuple(sorted(c)) for c in cols))
                        descriptions[key] += 1
assert len(descriptions) == 22680
assert set(descriptions.values()) == {2}
print("PASS: 22,680 height-nine multisets, each described exactly twice")
