"""Exact checks for the modular reductions and horizontal filler family."""

from itertools import combinations, product
from math import isqrt
from pathlib import Path
import json


def norm(v):
    return sum(t * t for t in v)


def mixed(a, b, c, d, modulus=None):
    side = tuple(v - u for u, v in zip(a, b))
    diagonal = tuple(v - u for u, v in zip(c, d))
    centers = tuple(u + v - x - y for x, y, u, v in zip(a, b, c, d))
    tests = (norm(side) - norm(diagonal), sum(u * v for u, v in zip(side, centers)))
    return all(t == 0 if modulus is None else t % modulus == 0 for t in tests)


def divisors(n):
    out = []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            out.append(d)
            if d * d != n:
                out.append(n // d)
    return sorted(out)


def main():
    inserted = [(0, r) for r in (0, 5)]
    sea = [(x, 0) for x in (3, 5, 6)] + [(x, 1) for x in (1, 2, 4)] + [(0, 3)]
    modular_cases = 0
    for central in product(inserted, repeat=3):
        for s in sea:
            points = central + (s,)
            for ab in combinations(range(4), 2):
                cd = tuple(i for i in range(4) if i not in ab)
                modular_cases += 1
                assert not mixed(*(points[i] for i in ab + cd), modulus=7)

    integer_cases = 0
    # These convenient physical rows verify the identity and distinct corners.
    # The uniform proof selects the rows from the actual large-height profile.
    r, filler = 10000, 1001
    for k in range(1, 101):
        factors = divisors(k * k)
        witnesses = 0
        for u in factors:
            v = k * k // u
            if u >= v:
                continue
            a, b = (-7 * u, filler), (7 * v, filler)
            c, d = (0, r), (7 * (v - u), r + 14 * k)
            white = ((-7 * u, r + 7 * k), (7 * v, r + 7 * k))
            assert mixed(a, b, c, d)
            assert norm(tuple(x - y for x, y in zip(c, d))) == norm(tuple(x - y for x, y in zip(*white)))
            assert tuple(x + y for x, y in zip(c, d)) == tuple(x + y for x, y in zip(*white))
            assert len({a, b, c, d, *white}) == 6
            assert norm(tuple(x - y for x, y in zip(c, d))) > 0
            witnesses += 1
            integer_cases += 1
        assert witnesses == (len(factors) - 1) // 2

    result = {"status": "PASS", "three_inserted_one_sea_pairings": modular_cases,
              "integer_horizontal_witnesses": integer_cases, "maximum_k": 100}
    output = Path(__file__).with_name("mod7_multilabel_reductions_check.json")
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
