"""Count the exact low/high mixed role in a finite row interval.

This is a geometric count, not a completed label-permutation search.
"""
from math import gcd, isqrt, log
from pathlib import Path
import json
import sys
import time


def run(height):
    started = time.monotonic()
    d = height - 1
    divisors = [[] for _ in range(d + 1)]
    for p in range(1, d + 1):
        for n in range(p, d + 1, p):
            divisors[n].append(p)
    candidates = squares = supports = modular = phase = 0
    example = None
    by_scale = {}
    for s in range(2, d, 2):
        for a in range(s + 2, d, 2):
            n = d - (a + s)//2
            for p in divisors[n]:
                m = n//p
                for k in divisors[s]:
                    q = s//k
                    if gcd(p, q) != 1:
                        continue
                    candidates += 1
                    norm = (k*p)**2 + s*s - a*a
                    if norm <= 0:
                        continue
                    v = isqrt(norm)
                    if v*v != norm:
                        continue
                    squares += 1
                    center = k*p + 2*m*q
                    assert (center-v) % 2 == 0
                    for sign in (-1, 1):
                        ax = (center + sign*v)//2
                        ex = (center - sign*v)//2
                        if len({0, k*p, ax, ex}) != 4:
                            continue
                        supports += 1
                        by_scale[p.bit_length()-1] = by_scale.get(p.bit_length()-1, 0)+1
                        g = d % 7
                        if not g or a % 7 or s % 7 != 3*g % 7 or ax % 7:
                            continue
                        for reflection in (1, -1):
                            bx, lx, cx = reflection*k*p, reflection*ex, reflection*ax
                            if bx % 7 not in (1, 2, 4) or lx % 7 not in (3, 5, 6):
                                continue
                            modular += 1
                            if a % 49 == 0:
                                continue
                            sigma = 1 if 5*g*(a//7) % 7 in (1, 2, 4) else -1
                            allowed = (0, 6) if sigma == 1 else (0, 1)
                            if (cx//7) % 7 not in allowed:
                                continue
                            phase += 1
                            if example is None:
                                example = dict(a=a, s=s, p=p, q=q, k=k, m=m, v=v,
                                               label_even=[0, d-s], high=[bx,d],
                                               label_odd=[cx,a], low=[lx,0], sigma=sigma)
    return dict(height=height, candidates=candidates, squares=squares,
                geometric_supports=supports, modular_supports=modular,
                two_phase_supports=phase, example=example,
                supports_over_h2_log=supports/(height*height*log(height)),
                supports_over_h2_log2=supports/(height*height*log(height)**2),
                by_primitive_horizontal_scale=by_scale,
                seconds=time.monotonic()-started)


if __name__ == "__main__":
    heights = list(map(int, sys.argv[1:])) or [64,128,256,512]
    results = []
    for height in heights:
        result = run(height)
        results.append(result)
        print(json.dumps(result), flush=True)
    Path(__file__).with_name("low_high_mixed_square_probe.json").write_text(
        json.dumps(dict(scope="Exact counts of the stated role only; no asymptotic claim.",
                        results=results), indent=2)+"\n", encoding="utf-8")
