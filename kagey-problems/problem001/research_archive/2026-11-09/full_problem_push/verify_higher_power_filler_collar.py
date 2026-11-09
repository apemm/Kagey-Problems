"""Check the six-point higher-power filler collar obstruction."""

from itertools import combinations

M = 49
L, F0, H = 1, 1003, 20866
A, B = (9898, 1591), (903, H)
C, D = (8575, 1003), (966, H)
P, Q = (9268, 1297), (273, 20572)
replacements = {903, 966}


def sub(a, b):
    return a[0] - b[0], a[1] - b[1]


def norm(v):
    return sum(x*x for x in v)


def rectangle(points):
    if len(set(points)) != 4:
        return False
    for a, b in combinations(points, 2):
        c, d = [p for p in points if p not in (a, b)]
        if (a[0]+b[0], a[1]+b[1]) == (c[0]+d[0], c[1]+d[1]):
            if norm(sub(a, b)) == norm(sub(c, d)):
                return True
    return False


def black(p):
    x, y = p
    if x in replacements:
        return y == H
    if x % 7 == 0:
        return y == F0 + 14*((x//7) % M)
    return y == (H if x % 7 in (1, 2, 4) else L)


assert (H-L) % 7 == 5
assert (F0-L) % 7 == 3*((H-L) % 7) % 7
assert all(0 <= x < 10000 and 1 <= y <= H for x, y in (A,B,C,D,P,Q))
assert all(black(p) for p in (A, B, C, D))
assert not black(P) and not black(Q)
assert rectangle((A, B, P, Q)) and rectangle((C, D, P, Q))
assert {p for p in (A, B, P, Q) if not black(p)} == {P, Q}
assert {p for p in (C, D, P, Q) if not black(p)} == {P, Q}
assert norm(sub(B,A)) == norm(sub(D,C)) == 452435650
print("PASS: two distinct rectangles have the same two-white presentation")

# A monotone high-hole tail, with the high row on the grid boundary.
H = 7426
A, B = (294, 1591), (3017, H)
C, D = (2058, 1003), (2513, H)
P, Q = (924, 1297), (3647, 7132)


def monotone_black(p):
    x, y = p
    if x % 7 == 0:
        return y == (H if x > 2401 else F0 + 14*((x//7) % M))
    return y == (H if x % 7 in (1, 2, 4) else L)


assert (H-L) % 7 == 5
assert all(0 <= x < 4000 and 1 <= y <= H for x, y in (A,B,C,D,P,Q))
assert all(monotone_black(p) for p in (A,B,C,D))
assert not monotone_black(P) and not monotone_black(Q)
assert rectangle((A,B,P,Q)) and rectangle((C,D,P,Q))
assert norm(sub(B,A)) == norm(sub(D,C)) == 41461954
print("PASS: the monotone high-hole tail also has a two-white collision")
