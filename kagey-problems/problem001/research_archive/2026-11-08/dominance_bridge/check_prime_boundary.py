"""Check the Diophantine obstruction used in the pinned Sidon bridge proof.

This checks both a direct divisor enumeration and the prime divisibility step.
The proof, rather than this finite enumeration, covers arbitrary height.
"""

import argparse
import json
from math import isqrt


def primes_up_to(n):
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p * p:n + 1:p] = b"\x00" * ((n - p * p) // p + 1)
    return [p for p in range(3, n + 1, 4) if sieve[p]]


def divisors(n):
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            yield d
            if d * d != n:
                yield n // d


def composite_witness():
    # Congruence 3 modulo 4 without primality does not suffice.
    first = {(0, 9), (80, 39), (3, 1), (83, 31)}
    second = {(0, 9), (80, 39), (4, 1), (76, 47)}
    side, connector = (80, 30), (3, -8)
    assert sum(a * b for a, b in zip(side, connector)) == 0
    assert 80 ** 2 + 30 ** 2 == 72 ** 2 + 46 ** 2
    assert (0 + 80, 9 + 39) == (4 + 76, 1 + 47)
    assert first ^ second == {(3, 1), (4, 1), (76, 47), (83, 31)}
    return {"s": 15, "t": 23, "x": 80, "r": 72,
            "rectangles": [sorted(first), sorted(second)]}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=1000)
    args = parser.parse_args()
    primes = primes_up_to(args.limit)
    pair_count = candidate_count = forced_divisibility = 0
    for i, s in enumerate(primes):
        assert all((x * x + 1) % s for x in range(s))
        for t in primes[i + 1:]:
            pair_count += 1
            delta = 4 * (t * t - s * s)
            for x in divisors(2 * s * (t - s)):
                candidate_count += 1
                if x * x < delta:
                    continue
                assert x > 2 * (t - s)
                assert x % s == 0
                forced_divisibility += 1
                value = x * x - delta
                assert value % s == (-4 * t * t) % s
                assert isqrt(value) ** 2 != value, (s, t, x, value)
    print(json.dumps({
        "prime_limit": args.limit,
        "primes_3_mod_4": len(primes),
        "distinct_prime_pairs": pair_count,
        "divisors_checked": candidate_count,
        "length_feasible_divisors": forced_divisibility,
        "mixed_boundary_solutions": 0,
        "composite_counterexample": composite_witness(),
    }, indent=2))


if __name__ == "__main__":
    main()
