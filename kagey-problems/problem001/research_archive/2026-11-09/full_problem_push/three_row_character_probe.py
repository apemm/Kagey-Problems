"""Conservative positive-support tests for period-seven three-row seas."""
from itertools import combinations, product
from math import isqrt
from pathlib import Path
import argparse
import json
import time
from threshold_progress_check import grouped, divisors

HERE = Path(__file__).resolve().parent


def mixed_patterns(h, levels):
    rows4 = set()
    for occupied in combinations(range(4), 2):
        other = [i for i in range(4) if i not in occupied]
        for r, s in product(range(1, h+1), repeat=2):
            for low in product(levels, repeat=2):
                rows = [0]*4
                rows[occupied[0]], rows[occupied[1]] = r, s
                rows[other[0]], rows[other[1]] = low
                rows4.add(tuple(rows))
    records = set()
    for a, b, c, d in rows4:
        y, v, sy = b-a, d-c, a+b-c-d
        candidates = []
        if y:
            if not sy:
                continue
            for x in divisors(abs(sy*y)):
                norm = x*x+y*y-v*v
                z = isqrt(norm) if norm >= 0 else -1
                if z < 0 or z*z != norm:
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
            cols = grouped((A, B, C, D))
            for center, required in cols.items():
                if len(required) > 2:
                    continue
                if len(required) == 2 and sum(required) % 2 == 0:
                    continue
                if all(len(rs) == 1 and next(iter(rs)) in levels
                       for col, rs in cols.items() if col != center):
                    records.add((tuple(sorted(required)),
                                 tuple(sorted((col-center, next(iter(rs)))
                                              for col, rs in cols.items()
                                              if col != center))))
    return records


def check(h, filler):
    levels = (1, h, filler)
    squares = {1, 2, 4}
    def sea(x):
        if x % 7 == 0:
            return filler
        return h if x % 7 in squares else 1
    forbidden = {}
    def reject(required, support, kind):
        forbidden.setdefault(tuple(sorted(required)), dict(kind=kind, support=support))
    for required, support in mixed_patterns(h, set(levels)):
        if all(sea(x) == r for x, r in support):
            reject(required, support, "mixed")
    for r in range(1, h+1):
        for s, t in product(levels, repeat=2):
            norm = -(s-r)*(t-r)
            if norm:
                for mag in divisors(abs(norm)):
                    for u in (mag, -mag):
                        v = norm//u
                        if (u, s) == (v, t):
                            continue
                        if sea(u) == s and sea(v) == t and 1 <= s+t-r <= h:
                            reject((r,), ((u, s), (v, t)), "three-central-angle")
            norm = (r-s)*(t-s)
            if norm:
                for mag in divisors(abs(norm)):
                    for u in (mag, -mag):
                        v = u+norm//u
                        if not v or v == u:
                            continue
                        if sea(u) == s and sea(v) == t and 1 <= r+t-s <= h:
                            reject((r,), ((u, s), (v, t)), "three-sea-angle")
    for a in range(1, h+1, 2):
        for b in range(2, h+1, 2):
            for s in levels:
                norm = -(s-a)*(s-b)
                u = isqrt(norm) if norm > 0 else 0
                if not u or u*u != norm:
                    continue
                if any(sea(x) == s for x in (u, -u)) and 1 <= a+b-s <= h:
                    reject((a, b), ((u, s),), "three-two-central")
    safe_rows = [r for r in range(1, h+1) if (r,) not in forbidden]
    safe = [(a, b) for a in safe_rows if a % 2
            for b in safe_rows if b % 2 == 0
            if tuple(sorted((a, b))) not in forbidden]
    return dict(height=h, filler=filler, safe_rows=safe_rows, safe_edges=safe,
                forbidden=[dict(required=k, **v) for k, v in sorted(forbidden.items())],
                convention="Sufficient: all three-black tilted rectangles rejected")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--height", type=int, default=30)
    parser.add_argument("--fillers")
    args = parser.parse_args()
    h = args.height
    assert h % 2 == 0 and (h-1) % 7
    fillers = (list(map(int, args.fillers.split(","))) if args.fillers else
               [r for r in range(2, h) if ((r-1)*pow(h-1, -1, 7)) % 7 in (3, 4, 5)])
    start = time.monotonic()
    out = []
    for filler in fillers:
        rec = check(h, filler)
        out.append(rec)
        print(json.dumps({k: v for k, v in rec.items()
                          if k not in ("forbidden", "safe_edges")}),
              len(rec["safe_edges"]), flush=True)
        (HERE/f"three_row_character_h{h}.json").write_text(json.dumps(
            dict(records=out, seconds=time.monotonic()-start), indent=2)+"\n")


if __name__ == "__main__":
    main()
