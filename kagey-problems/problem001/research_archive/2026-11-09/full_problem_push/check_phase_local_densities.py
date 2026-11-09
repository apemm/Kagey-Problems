"""Exact residue checks for protected-phase local density tables."""
from fractions import Fraction
from itertools import product
import json
from pathlib import Path

def q(n):
    return n * (n - 1) // 2 % 2

def accepted(points):
    return (
        all(y % 2 == 0 for x, y in points),
        all((x + y) % 2 == 0 for x, y in points),
        all((q(x) + q(y)) % 2 == 0 for x, y in points),
    )

def corners(a, b, k, ell):
    return [(0, 0), (k*a, k*b), (-ell*b, ell*a),
            (k*a-ell*b, k*b+ell*a)]

def fractions(counts, total):
    return [str(Fraction(x, total)) for x in counts]

def hidden_check(a, b):
    counts = [0, 0, 0]
    total = 0
    for k, ell, px, py in product(range(4), repeat=4):
        pts = [(px+x, py+y) for x, y in corners(a, b, k, ell)]
        for i, ok in enumerate(accepted(pts)):
            counts[i] += ok
        total += 1
    expected = (["1/8", "1/2", "1/4"] if a % 2 and b % 2
                else ["1/4", "1/8", "1/8"])
    actual = fractions(counts, total)
    assert actual == expected, (a, b, actual)
    return {"direction": [a, b], "fractions": actual}

def six_check(first, second):
    counts = [0, 0, 0]
    total = 0
    for k, ell, s, t, px, py in product(range(4), repeat=6):
        # Include the common corner. The rectangle identity makes this
        # equivalent to testing the six nonshared corners.
        pts = corners(*first, k, ell) + corners(*second, s, t)[1:]
        pts = [(px+x, py+y) for x, y in pts]
        for i, ok in enumerate(accepted(pts)):
            counts[i] += ok
        total += 1
    types = sum(int(a % 2 and b % 2) for a, b in [first, second])
    expected = {
        2: ["1/32", "1/2", "1/8"],
        1: ["1/16", "1/8", "1/16"],
        0: ["1/8", "1/32", "1/32"],
    }[types]
    actual = fractions(counts, total)
    assert actual == expected, (first, second, actual)
    return {"directions": [first, second], "fractions": actual}

def mixed_check(a, b, c, d, k):
    assert a*a+b*b == c*c+d*d
    orbit = sorted({(sx*u, sy*v)
                    for u, v in [(c, d), (d, c)]
                    for sx, sy in product([-1, 1], repeat=2)})
    assert len(orbit) == 8
    assert (a, b) not in orbit and (-a, -b) not in orbit
    counts = [0, 0, 0]
    total = 0
    compatible = 0
    ux, uy = k*a, k*b
    for vx0, vy0 in orbit:
        vx, vy = k*vx0, k*vy0
        if (ux+vx) % 2 or (uy+vy) % 2:
            continue
        compatible += 1
        for ell, px, py in product(range(4), repeat=3):
            tx, ty = -ell*b, ell*a
            pts = [(tx, ty), (tx+ux, ty+uy),
                   ((ux+vx)//2, (uy+vy)//2),
                   ((ux-vx)//2, (uy-vy)//2)]
            pts = [(px+x, py+y) for x, y in pts]
            for i, ok in enumerate(accepted(pts)):
                counts[i] += ok
            total += 1
    odd_odd = bool(a % 2 and b % 2)
    valuation_class = 0 if k % 2 else (1 if k % 4 else 2)
    expected = {
        (True, 0): ["0", "1/4", "1/8"],
        (True, 1): ["1/4", "1/2", "1/4"],
        (True, 2): ["1/4", "1/2", "3/8"],
        (False, 0): ["1/4", "0", "1/8"],
        (False, 1): ["1/4", "1/4", "0"],
        (False, 2): ["1/4", "1/4", "1/4"],
    }[odd_odd, valuation_class]
    if not odd_odd and a % 2 == 0:
        expected = expected.copy()
        expected[0] = ["0", "1/4", "1/2"][valuation_class]
    actual = fractions(counts, total)
    assert actual == expected, (a, b, c, d, k, actual)
    return {"direction": [a, b], "other_representation": [c, d],
            "scale": k, "compatible_orbit_members": compatible,
            "fractions": actual}

def main():
    hidden = [hidden_check(a, b) for a, b in
              [(1,1),(1,3),(3,1),(3,7),(1,2),(2,1),
               (1,4),(4,1),(3,2),(2,3)]]
    six = [six_check(first, second) for first, second in
           [((1,1),(1,3)), ((1,1),(1,2)), ((1,2),(2,3))]]
    mixed = [mixed_check(a,b,c,d,k)
             for a,b,c,d in [(1,17,11,13),(3,11,7,9),
                             (1,8,4,7),(2,9,6,7)]
             for k in [1,2,4,8]]
    result = {"status": "passed", "hidden": hidden, "six": six,
              "mixed": mixed}
    dest = Path(__file__).with_suffix(".json")
    dest.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"Passed {len(hidden)} hidden, {len(six)} six-cell, "
          f"and {len(mixed)} mixed residue checks.")
    print(dest)

if __name__ == "__main__":
    main()

