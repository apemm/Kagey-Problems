"""Exact checks for the affine obstruction and joined-clique construction."""
from pathlib import Path
from itertools import product
from math import isqrt, prod
import json

HERE = Path(__file__).resolve().parent


def vertical_rival(h, a, other_a, other_b):
    x = 2 * (a - other_a)
    y = a - other_b
    length = isqrt(x * x + y * y)
    assert length * length == x * x + y * y
    assert (a + other_b - length) % 2 == 0
    low = (a + other_b - length) // 2
    high = (a + other_b + length) // 2
    assert 1 <= low < high <= h and (high - low) % 2 == 1


def main():
    affine = 0
    for alpha, beta, modulus in product(range(-5, 6), range(-5, 6), range(1, 9)):
        if beta == 0:
            continue
        d = 2 * abs(beta) * modulus * (abs(alpha) + abs(beta) + 2)
        q = alpha * d // beta
        a = d * d + 2 * abs(q) + 1
        h = a + 1
        other_a = a - d
        other_b = a - d * d + 1
        b = other_b - q
        assert all(1 <= row <= h for row in (a, b, other_a, other_b))
        assert a % 2 == other_a % 2 == 1 and b % 2 == other_b % 2 == 0
        assert alpha * a + beta * b == alpha * other_a + beta * other_b
        assert a % modulus == other_a % modulus and b % modulus == other_b % modulus
        vertical_rival(h, a, other_a, other_b)
        affine += 1
    cliques = []
    primes = [3, 5, 7, 11, 13, 17]
    for count in range(7):
        q = prod(primes[:count])
        divisors = [1]
        for prime in primes[:count]:
            divisors = [d * prime ** e for d in divisors for e in range(3)]
        h = 8 * q * q + 6
        a = 4 * q * q + 3
        other_a = a - 2 * q
        targets = set()
        for u in divisors:
            v = 4 * q * q // u
            for b in (a - abs(v - u), a + abs(v - u)):
                assert 1 <= b <= h and b % 2 == 0
                vertical_rival(h, a, other_a, b)
                targets.add(b)
        assert len(targets) == 2 * 3 ** count
        cliques.append({'primes': count, 'height': h,
                        'row_clique': h // 2, 'additional_vertices': len(targets)})
    result = {'status': 'PASS', 'affine_checks': affine, 'joined_cliques': cliques}
    (HERE / 'global_P_coloring_obstructions_check.json').write_text(
        json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
