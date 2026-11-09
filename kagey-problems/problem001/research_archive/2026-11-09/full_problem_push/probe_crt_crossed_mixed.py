"""Bounded exact search for inserted-only crossed mixed CRT supports.

Only opposite-parity black sides are needed after the modular reductions.
The search uses actual strip containment and the 98-divisible connector.
"""

from bisect import bisect_right
from math import gcd, isqrt
from pathlib import Path
import json
import sys
import time


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, isqrt(n) + 1, 2))


def next_prime(n):
    n += 1
    while n % 8 not in (3, 5) or not is_prime(n):
        n += 1
    return n


def ceildiv(a, b):
    return -((-a) // b)


def search(h, seconds):
    begin = time.monotonic()
    p = next_prime(4 * h)
    q = next_prime(p)
    M = 98 * p * q
    ip, iq, ipq = pow(98, -1, p), pow(98, -1, q), pow(p, -1, q)
    cols = {}
    for a in range(1, h + 1, 2):
        ra = a * ip % p
        for b in range(2, h + 1, 2):
            rb = b * iq % q
            x = 98 * (ra + p * ((rb - ra) * ipq % q))
            assert x not in cols
            cols[x] = (a, b)
    positions = sorted(cols)
    H = h - 1
    max_gap = H * H // (4 * 98)
    norm_cache = {}
    pairs = sides = connectors = diagonal_tests = 0

    def vectors(square):
        old = norm_cache.get(square)
        if old is not None:
            return old
        out = []
        lower = isqrt(max(0, square - H * H))
        for vx in range(98 * ceildiv(lower, 98), isqrt(square) + 1, 98):
            yy = square - vx * vx
            vy = isqrt(yy)
            if vy > H or vy * vy != yy or vy % 2 != 1:
                continue
            for sx in ({vx, -vx} if vx else {0}):
                out.append((sx, vy))
                out.append((sx, -vy))
        norm_cache[square] = out
        return out

    for i, x in enumerate(positions):
        if i % 1000 == 0 and time.monotonic() - begin > seconds:
            return {"status": "INCOMPLETE", "height": h, "primes": [p, q],
                    "columns_processed": i, "columns_total": len(positions),
                    "pairs": pairs, "sides": sides, "connectors": connectors,
                    "diagonal_tests": diagonal_tests, "seconds": time.monotonic() - begin}
        end = bisect_right(positions, x + max_gap, i + 1)
        for j in range(i + 1, end):
            z = positions[j]
            u = z - x
            pairs += 1
            for a, b in ((cols[x][0], cols[z][1]), (cols[x][1], cols[z][0])):
                v = b - a
                assert v % 2 != 0
                sides += 1
                gg = gcd(abs(v), 98 * u)
                tx0 = 98 * abs(v) // gg
                ty0 = -98 * u // gg * (1 if v > 0 else -1)
                # The entire side and its translate must fit vertically.
                low_y, high_y = 1 - min(a, b), h - max(a, b)
                if ty0 > 0:
                    lower, upper = ceildiv(low_y, ty0), high_y // ty0
                else:
                    lower, upper = ceildiv(high_y, ty0), low_y // ty0
                # Both translated side endpoints must also lie in the board.
                lower = max(lower, ceildiv(-x, tx0))
                upper = min(upper, (M - 1 - z) // tx0)
                if lower == upper == 0 or lower > upper:
                    continue
                alt = vectors(u * u + v * v)
                for scale in range(lower, upper + 1):
                    if not scale:
                        continue
                    tx, ty = scale * tx0, scale * ty0
                    assert u * tx + v * ty == 0
                    A, B = (x, a), (z, b)
                    W, Z = (x + tx, a + ty), (z + tx, b + ty)
                    assert all(0 <= xx < M and 1 <= yy <= h for xx, yy in (A, B, W, Z))
                    connectors += 1
                    xs, ys = W[0] + Z[0], W[1] + Z[1]
                    for vx, vy in alt:
                        diagonal_tests += 1
                        if (xs - vx) % 196 or (ys - vy) % 2:
                            continue
                        cx, cy = (xs - vx) // 2, (ys - vy) // 2
                        dx, dy = xs - cx, ys - cy
                        if cy not in cols.get(cx, ()) or dy not in cols.get(dx, ()):
                            continue
                        C, D = (cx, cy), (dx, dy)
                        r1, r2 = {A, B, W, Z}, {C, D, W, Z}
                        if len(r2) != 4 or r1 == r2:
                            continue
                        assert len(r1) == 4
                        assert all(yy in cols.get(xx, ()) for xx, yy in r1 ^ r2)
                        assert (dx - cx) ** 2 + (dy - cy) ** 2 == u * u + v * v
                        return {"status": "COUNTEREXAMPLE", "height": h, "primes": [p, q],
                                "width": M, "black_side": [A, B], "black_diagonal": [C, D],
                                "common_pair": [W, Z], "owner_labels": {str(xx): cols[xx]
                                  for xx, yy in (A, B, C, D)}, "norm": u * u + v * v,
                                "columns_processed": i, "pairs": pairs, "sides": sides,
                                "connectors": connectors, "diagonal_tests": diagonal_tests,
                                "seconds": time.monotonic() - begin}
    return {"status": "NO_CROSSED_MIXED", "height": h, "primes": [p, q],
            "columns_total": len(positions), "pairs": pairs, "sides": sides,
            "connectors": connectors, "diagonal_tests": diagonal_tests,
            "seconds": time.monotonic() - begin}


def main():
    heights = [int(v) for v in sys.argv[1].split(",")] if len(sys.argv) > 1 else [200, 300, 500, 750, 1000]
    seconds = float(sys.argv[2]) if len(sys.argv) > 2 else 60.0
    output = Path(__file__).with_name("crt_crossed_mixed_probe.jsonl")
    for h in heights:
        result = search(h, seconds)
        with output.open("a", encoding="utf-8") as f:
            f.write(json.dumps(result) + "\n")
        print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
