"""Exact CRT coordinates and rectangle certificates for the chain families."""

from math import isqrt
from pathlib import Path
import json


def prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, isqrt(n) + 1, 2))


def next_prime(n):
    n += 1
    while not prime(n):
        n += 1
    return n


def center(a, b, P, Q, p, q):
    rp = P * a * pow(98 * Q, -1, p) % p
    rq = P * b * pow(98 * Q, -1, q) % q
    j = rp + p * ((rq - rp) * pow(p, -1, q) % q)
    return 98 * j


def run(P, Q, v=1, small=False):
    assert P % 2 == 0 and Q % 2 == 1 and v % 2 == 1
    if small:
        assert (P, Q) == (4, 3)
        a, b = 49 * v + 2, 490 * v + 2
        c, d = 343 * v + 2, 784 * v + 2
        height = 833 * v + 2
        expected_gap = 392 * v
    else:
        r = 1
        while (49 * P * r) ** 2 - 98 * Q * r - 1 <= 0:
            r += 1
        T = (49 * P * r) ** 2 - 98 * Q * r - 1
        a, b = v + 2, (T + 1) * v + 2
        c, d = (98 * Q * r + 1) * v + 2, (49 * P * r) ** 2 * v + 2
        height = ((49 * P * r) ** 2 + 1) * v + 2
        expected_gap = 98 * P * r * v
    assert a % 2 == c % 2 == 1 and b % 2 == d % 2 == 0
    assert b - a == d - c > 0
    p = next_prime((P * P + Q * Q + P + Q + 3) * height)
    q = next_prime(p)
    x = center(a, b, P, Q, p, q)
    z = center(c, d, P, Q, p, q)
    assert z - x == expected_gap
    assert Q * (z - x) == P * (c - a) == P * (d - b)
    length2 = (z - x) ** 2 + (d - a) ** 2
    length = isqrt(length2)
    assert length * length == length2
    assert (x + z) % 2 == (a + d - length) % 2 == 0
    middle = (x + z) // 2
    low, high = (a + d - length) // 2, (a + d + length) // 2
    assert (low, high) == (2, height)
    owner = center(high, low, P, Q, p, q)
    assert owner != middle
    diagonal_rect = {(x, a), (z, d), (middle, low), (middle, high)}
    axis_rect = {(owner, low), (owner, high), (middle, low), (middle, high)}
    required_black = {(x, a), (z, d), (owner, low), (owner, high)}
    assert len(diagonal_rect) == len(axis_rect) == 4
    assert diagonal_rect ^ axis_rect == required_black
    assert all(1 <= row <= height for _, row in diagonal_rect | axis_rect)
    assert x + z == 2 * middle and a + d == low + high
    assert length2 == (high - low) ** 2
    return {"P": P, "Q": Q, "v": v, "small": small, "height": height,
            "offset": b - a, "primes": [p, q], "gap": z - x,
            "labels": [[a, b], [c, d]], "centers": [x, z],
            "axis_owner": owner, "white_column": middle,
            "white_rows": [low, high], "norm": length2}


def main():
    cases = [run(P, Q) for P, Q in ((4, 3), (12, 5), (8, 15), (20, 21))]
    cases += [run(4, 3, v, small=True) for v in (1, 3, 5)]
    result = {"status": "PASS", "scope": "exact certificates, not a density experiment",
              "cases": cases}
    path = Path(__file__).with_name("crt_chain_obstruction_check.json")
    path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "PASS", "cases": len(cases)}))


if __name__ == "__main__":
    main()
