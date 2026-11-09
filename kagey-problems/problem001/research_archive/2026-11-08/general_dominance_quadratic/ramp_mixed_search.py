"""Search exact two-tail-point mixed collisions in the modular-ramp splice.

This enumerates arithmetic collision parameters, not sea states or SCCs.
"""
from math import isqrt
import argparse
import json
from pathlib import Path
import time


def representative(lo, hi, residue, p):
    a = lo + (residue - lo) % p
    return a if a <= hi else None


def certificate(p, A, B, C, D):
    U = (B[0] - A[0], B[1] - A[1])
    V = (D[0] - C[0], D[1] - C[1])
    H = (A[0] + B[0] - C[0] - D[0],
         A[1] + B[1] - C[1] - D[1])
    if len({A, B, C, D}) < 4 or not U[0] or not U[1]:
        return None
    if H == (0, 0) or H[0] % 2 or H[1] % 2:
        return None
    if V == U or V == (-U[0], -U[1]):
        return None
    assert sum(x*x for x in U) == sum(x*x for x in V)
    assert sum(x*y for x, y in zip(U, H)) == 0
    W = (A[0] - H[0] // 2, A[1] - H[1] // 2)
    Z = (B[0] - H[0] // 2, B[1] - H[1] // 2)
    if not (0 <= W[1] < p and 0 <= Z[1] < p):
        return None
    black = lambda P: P[1] == (P[0] % p if P[0] < 0 else p - 2)
    assert all(black(P) for P in (A, B, C, D))
    R1, R2 = {A, B, W, Z}, {C, D, W, Z}
    assert len(R1) == len(R2) == 4 and R1 != R2
    white1 = sorted(P for P in R1 if not black(P))
    white2 = sorted(P for P in R2 if not black(P))
    assert white1 == white2
    return {"prime": p, "side_black": [A, B], "diagonal_black": [C, D],
            "common_pair": [W, Z], "white_presentation": white1,
            "rectangle_1": sorted(R1), "rectangle_2": sorted(R2)}


def divisors(n):
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            yield d
            if d*d != n:
                yield n//d


def search_two_pins(p):
    c = p - 2
    for v in range(-1, p-1):
        if not v:
            continue
        r = c - v
        for f in range(-1, p-1):
            if f == v:
                continue
            s = c - f
            Hy = f-v
            if Hy % 2:
                continue
            for d in divisors(abs(Hy*v)):
                Hx = -Hy*v//d
                if Hx % 2:
                    continue
                e2 = d*d+v*v-f*f
                if e2 <= 0:
                    continue
                e = isqrt(e2)
                if e*e != e2 or (d-e-Hx) % 2:
                    continue
                z = (d-e-Hx)//2
                if (r+z-s) % p:
                    continue
                x = representative(max(-d,-e-z), min(-1,-1-z), r, p)
                if x is not None:
                    out = certificate(p, (x,r), (x+d,c),
                                      (x+z,s), (x+z+e,c))
                    if out:
                        out["case"] = "two pins"
                        return out
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("primes", nargs="+", type=int)
    args = parser.parse_args()
    out = []
    for p in args.primes:
        assert pow(2, (p-1)//2, p) == p-1
        started = time.monotonic()
        result = search_two_pins(p)
        entry = {"prime": p, "collision": result,
                 "elapsed_seconds": time.monotonic()-started}
        out.append(entry)
        print(json.dumps(entry), flush=True)
        if result:
            break
    Path(__file__).with_suffix(".json").write_text(
        json.dumps(out, indent=2)+"\n", encoding="utf-8")


if __name__ == "__main__":
    main()
