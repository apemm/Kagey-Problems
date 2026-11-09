"""Bounded one-double support tests in quadratic-character binary seas."""
from itertools import combinations, product
from math import isqrt
from pathlib import Path
import argparse
import json
import time
from threshold_progress_check import tilts, mixed_supports, grouped, divisors

HERE = Path(__file__).resolve().parent


def restricted_mixed(h):
    row_tuples = set()
    for occupied in combinations(range(4), 2):
        other = [i for i in range(4) if i not in occupied]
        for r, s in product(range(1, h+1), repeat=2):
            for low in product((1, h), repeat=2):
                rows = [0]*4
                rows[occupied[0]], rows[occupied[1]] = r, s
                rows[other[0]], rows[other[1]] = low
                row_tuples.add(tuple(rows))
    out = set()
    for a, b, c, d in row_tuples:
        y, v, sy = b-a, d-c, a+b-c-d
        candidates = []
        if y:
            if not sy:
                continue
            for x in divisors(abs(sy*y)):
                q = x*x+y*y-v*v
                z = isqrt(q) if q >= 0 else -1
                if z < 0 or z*z != q:
                    continue
                for zz in {z, -z}:
                    candidates.append((x, zz, -sy*y//x))
        elif v and sy:
            for f in divisors(v*v):
                g = v*v//f
                if (f+g) % 2 == 0:
                    candidates.append(((f+g)//2, (g-f)//2, 0))
        for x, z, hx in candidates:
            if hx % 2 or (x-hx-z) % 2 or (c+d-y) % 2:
                continue
            if (z, v) in ((x, y), (-x, -y)):
                continue
            A, B = (0, a), (x, b)
            C, D = ((x-hx-z)//2, c), ((x-hx+z)//2, d)
            W, Z = (-hx//2, (c+d-y)//2), (x-hx//2, (c+d+y)//2)
            if not (1 <= W[1] <= h and 1 <= Z[1] <= h):
                continue
            if len({A, B, C, D, W, Z}) != 6:
                continue
            low = min(A[0], B[0], C[0], D[0])
            out.add(tuple(sorted((u-low, r) for u, r in (A, B, C, D))))
    return out


def local_patterns(h):
    records = set()
    raw = restricted_mixed(h)
    for r in range(2, h):
        norm = (r-1)*(h-r)
        for u in divisors(norm):
            v = norm//u
            for sign in (-1, 1):
                raw.add(tuple(sorted(((0, r), (sign*u, 1), (sign*v, h)))))
    for support in raw:
        cols = grouped(support)
        for center, rows in cols.items():
            if len(rows) > 2 or (len(rows) == 2 and sum(rows) % 2 == 0):
                continue
            if all(len(rs) == 1 and rs <= {1, h}
                   for x, rs in cols.items() if x != center):
                records.add((tuple(sorted(rows)),
                             tuple(sorted((x-center, next(iter(rs)))
                                          for x, rs in cols.items() if x != center))))
    return sorted(records)


def check_height(h, primes):
    patterns = local_patterns(h)
    edges = [(a, b) for a in range(1, h+1, 2) for b in range(2, h+1, 2)]
    covered = set()
    records = []
    for p in primes:
        for flip in (0, 1):
            for zero in (1, h):
                def row(x):
                    z = x % p
                    if z == 0:
                        return zero
                    positive = pow(z, (p-1)//2, p) == 1
                    return h if positive ^ bool(flip) else 1
                active = [(required, sea) for required, sea in patterns
                          if all(row(x) == y for x, y in sea)]
                good = [edge for edge in edges
                        if not any(set(required) <= set(edge) for required, sea in active)]
                covered.update(good)
                records.append(dict(prime=p, flip=flip, zero=zero, safe_edges=good,
                                    active_patterns=len(active),
                                    first_obstruction=active[0] if active else None))
    return dict(height=h, local_patterns=len(patterns), covered_edges=sorted(covered),
                uncovered_edges=[e for e in edges if e not in covered], records=records)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--maxheight", type=int, default=16)
    parser.add_argument("--minheight", type=int, default=4)
    parser.add_argument("--step", type=int, default=2)
    args = parser.parse_args()
    start = time.monotonic()
    records = []
    for h in range(args.minheight, args.maxheight+1, args.step):
        result = check_height(h, (3, 7, 11, 19, 23, 31, 43, 47))
        records.append(result)
        print(json.dumps(dict(height=h, covered=len(result["covered_edges"]),
                              total=h*h//4, patterns=result["local_patterns"])), flush=True)
        (HERE/"character_sea_probe.json").write_text(json.dumps(
            dict(records=records, seconds=time.monotonic()-start), indent=2)+"\n")


if __name__ == "__main__":
    main()
