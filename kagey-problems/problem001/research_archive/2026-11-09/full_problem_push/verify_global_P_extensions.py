"""Arithmetic checks for the linear-level palette and conic reduction."""
from itertools import permutations
from math import isqrt
from pathlib import Path
import json


def valuation(n, p):
    result = 0
    while n % p == 0:
        result += 1
        n //= p
    return result


def p_free(labels, height):
    for (a, _), (c, d) in permutations(labels, 2):
        norm = 4 * (a-c)**2 + (a-d)**2
        root = isqrt(norm)
        if root * root == norm and root <= height-1:
            return False
    return True


def rectangle(points):
    points = set(points)
    if len(points) != 4:
        return False
    for a in points:
        rest = points - {a}
        for b in rest:
            for c in rest - {b}:
                d = (b[0]+c[0]-a[0], b[1]+c[1]-a[1])
                if d in points - {a,b,c}:
                    u = (b[0]-a[0], b[1]-a[1])
                    v = (c[0]-a[0], c[1]-a[1])
                    if u[0]*v[0]+u[1]*v[1] == 0:
                        return True
    return False


def hidden_certificate(labels):
    a,b,c,d = [(2*(x-1),y) for x,y in labels]
    m = ((a[0]+b[0])//2, (a[1]+b[1])//2)
    n = ((c[0]+d[0])//2, (c[1]+d[1])//2)
    assert rectangle((a,b,c,d))
    assert rectangle((a,m,c,n))
    assert rectangle((m,b,n,d))
    black = {(2*(x-1),y) for x,z in labels for y in (x,z)}
    assert m not in black and n not in black
    assert set((a,m,c,n))-black == set((m,b,n,d))-black == {m,n}
    return [m,n]


def main():
    identities = 0
    for k in range(-6,7):
        for a in range(1,30,2):
            for b in range(2,31,2):
                t = b+k*a
                for s in range(1,30,2):
                    if a == s:
                        continue
                    norm = (s-b)**2+4*(s-a)**2
                    A = k*k+4
                    X = A*a+k*(s-t)-4*s
                    assert X*X-A*norm == -4*((k+1)*s-t)**2
                    assert (k+1)*s-t != 0
                    identities += 1

    solutions = 0
    for u in range(1,501):
        for v in range(1,501):
            if u == v:
                continue
            norm = u*u+4*v*v
            if norm % 5:
                continue
            L = isqrt(norm//5)
            if 5*L*L != norm:
                continue
            assert valuation(u,2)-valuation(v,2) in (0,2)
            assert valuation(u,5) == valuation(v,5)
            solutions += 1

    small = [(1,12),(3,20),(11,2),(13,10)]
    assert p_free(small,20)
    assert len({b for a,b in small}) == 4
    assert len({b+4*a for a,b in small}) == 4
    whites = hidden_certificate(small)

    families = []
    for values in ([],[0],[0,4],[-6,-2,0,1,4,7],list(range(12))):
        r = 11+max([0]+[abs(k) for k in values])
        t = 8*(r+2)**2
        labels = [(1,2*t),(3,2*t+2*r),
                  (2*r+1,2*t-8),(2*r+3,2*t+2*r-8)]
        height = 2*t+2*r
        assert p_free(labels,height)
        for k in values:
            assert len({b+k*a for a,b in labels}) == 4
        shared = hidden_certificate(labels)
        assert all(1 <= y <= height for x,y in shared)
        families.append({"levels":values,"height":height,
                         "labels":labels,"shared_whites":shared})

    output = {"status":"PASS","completed_square_identity_checks":identities,
              "nontrivial_conic_solutions_checked":solutions,
              "conic_coordinate_bound":500,
              "height_twenty_shared_whites":whites,
              "finite_level_counterexamples":families}
    path = Path(__file__).with_name("global_P_extensions_arithmetic_check.json")
    path.write_text(json.dumps(output,indent=2)+"\n")
    print(json.dumps({k:v for k,v in output.items()
                      if k != "finite_level_counterexamples"}))


if __name__ == "__main__":
    main()

