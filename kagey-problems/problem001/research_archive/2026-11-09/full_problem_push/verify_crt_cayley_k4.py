"""Exact actual-strip K4 certificate for the 4/3 CRT P-chain graph."""
import itertools
import json
from fractions import Fraction
from math import isqrt
from pathlib import Path


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def next_prime(n):
    n += 1
    while not prime(n):
        n += 1
    return n


def main():
    for r in range(4, 30):
        z = 3 + 2 ** r
        d = Fraction(2 * (z - 3), 25 - z * z)
        assert d == Fraction(2 ** (r - 3),
                             1 - 3 * 2 ** (r - 3) - 2 ** (2 * r - 4))
        assert d.denominator % 2 == 1
        assert d.numerator % (2 ** (r - 3)) == 0
        assert d.numerator % (2 ** (r - 2)) != 0
        assert 25 * d * d + 6 * d + 1 == (1 + z * d) ** 2
    h = 62182
    p = next_prime(25 * h)
    q = next_prime(p)
    modulus = 98 * p * q

    def center(a, b):
        assert 1 <= a <= h and a % 2 == 1
        assert 1 <= b <= h and b % 2 == 0
        rp = 4 * a * pow(294, -1, p) % p
        rq = 4 * b * pow(294, -1, q) % q
        z = rp + p * ((rq - rp) * pow(p, -1, q) % q)
        x = 98 * z
        assert 0 <= x < modulus and x % 98 == 0
        assert (3 * x - 4 * a) % p == 0
        assert (3 * x - 4 * b) % q == 0
        return x

    rows = [(785, 19160), (7547, 25922),
            (20777, 39152), (39887, 58262)]
    xs = [center(a, b) for a, b in rows]
    relative = [x - xs[0] for x in xs]
    assert relative == [0, 9016, 26656, 52136]
    out = []
    for i, j in itertools.combinations(range(4), 2):
        found = []
        for ri, rj in [(rows[i][0], rows[j][1]),
                       (rows[i][1], rows[j][0])]:
            dx = xs[j] - xs[i]
            n = dx * dx + (rj - ri) ** 2
            length = isqrt(n)
            if length * length != n:
                continue
            assert (ri + rj - length) % 2 == 0
            lo = (ri + rj - length) // 2
            hi = (ri + rj + length) // 2
            if not 1 <= lo < hi <= h:
                continue
            middle = (xs[i] + xs[j]) // 2
            assert (xs[i] + xs[j]) % 2 == 0
            a, b = (lo, hi) if lo % 2 else (hi, lo)
            owner = center(a, b)
            assert owner != middle
            black = {(xs[i], ri), (xs[j], rj),
                     (owner, lo), (owner, hi)}
            shared = {(middle, lo), (middle, hi)}
            tilted = shared | {(xs[i], ri), (xs[j], rj)}
            axis = shared | {(owner, lo), (owner, hi)}
            assert len(black) == len(tilted) == len(axis) == 4
            assert tilted ^ axis == black
            assert (xs[i] + xs[j], ri + rj) == (2 * middle, lo + hi)
            assert n == (hi - lo) ** 2
            found.append({"length": length, "white_rows": [lo, hi],
                          "white_column": middle,
                          "axis_owner_label": [a, b],
                          "axis_owner_column": owner})
        assert found, (i, j)
        out.append({"pair": [i, j], "rivals": found})
    result = {"status": "PASS", "generator_checks": 26,
              "height": h, "primes": [p, q],
              "modulus": modulus, "labels": rows, "columns": xs,
              "relative_columns": relative, "edges": out}
    target = Path(__file__).with_name("crt_cayley_k4_check.json")
    target.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "PASS", "height": h,
                      "edges": len(out), "primes": [p, q]}))


if __name__ == "__main__":
    main()
