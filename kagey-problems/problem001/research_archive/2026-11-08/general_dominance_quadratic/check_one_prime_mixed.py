"""Verify the exact mixed certificate in one_prime_mixed_obstruction.md."""

import json
from math import isqrt


def norm(v):
    return sum(x*x for x in v)


def sub(a, b):
    return tuple(x-y for x, y in zip(a, b))


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def main():
    k = 24
    t, c = 16*k*k+16*k+5, 8*k+2
    p, h = (k*t-c)//2, t+c+1
    assert p > 10*h
    assert all(p % d for d in range(2, isqrt(p)+1))
    b1, b2 = (t-3)//2, (t+1)//2
    indices = [(1, b1), (c+1, b2), (0, b1), (c+1, b2)]
    for a, b in indices:
        assert 0 <= a < (h+1)//2 and 0 <= b < h//2
    rows = [3, t+3, t-1, 2*c+3]
    points = [((4*(a+p*b)), r) for (a, b), r in zip(indices, rows)]
    for (a, b), (_, r) in zip(indices, points):
        assert r in (2*a+1, 2*b+2)
    a, b, cp, d = points
    w, z = (a[0]-2, c+1), (b[0]-2, t+c+1)
    u, v, shift = sub(b, a), sub(d, cp), sub(w, a)
    assert add(a, z) == add(b, w)
    assert sum(x*y for x, y in zip(u, shift)) == 0
    assert norm(u) and norm(shift)
    assert add(cp, d) == add(w, z)
    assert norm(v) == norm(sub(z, w)) == norm(u)
    assert v not in (u, tuple(-x for x in u))
    assert all(1 <= pt[1] <= h for pt in points+[w, z])
    assert w[0] % 4 == z[0] % 4 == 2
    r1, r2 = {a, b, w, z}, {cp, d, w, z}
    assert len(r1) == len(r2) == 4 and r1 != r2
    marked = set(points)
    assert r1-marked == r2-marked == {w, z}
    assert r1 ^ r2 == marked
    print(json.dumps({"height": h, "prime": p, "k": k,
                      "marked_points": points, "white_pair": [w, z],
                      "side_vector": u, "other_diagonal": v,
                      "squared_length": norm(u), "verified": True}, indent=2))


if __name__ == "__main__":
    main()
