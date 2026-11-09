"""Independent factorization check of the first minimum-width discrepancy."""

import json
from math import isqrt


def restricted(n):
    best, witness = n, (n-1, 1, 1)
    y = 2
    while y < best:
        x = (n-1)//y
        if x == 0:
            break
        z = n-x*y
        if x+y*z < best:
            best, witness = x+y*z, (x, y, z)
        y += 1
    return best, witness


def rectangle_minimum(n, upper):
    # A leftmost-corner parametrization has height b+d=n and ac=bd.
    # Its width is a+c. This search is independent of the primitive-direction
    # quadruple enumeration in minimum_width_audit.py.
    best, witness = upper, None
    b = 1
    while 2*b <= n:
        product = b*(n-b)
        if 4*product >= best*best:
            break
        for a in range(1, isqrt(product)+1):
            if product % a == 0:
                c = product//a
                if a+c < best:
                    best, witness = a+c, (a, c, b, n-b)
        b += 1
    return best, witness


def main():
    failures = []
    for n in range(2, 656):
        upper, restricted_witness = restricted(n)
        value, factor_witness = rectangle_minimum(n, upper)
        if value < upper:
            failures.append({"height_span": n, "actual_minimum": value,
                             "restricted_minimum": upper,
                             "restricted_witness": restricted_witness,
                             "factor_witness": factor_witness})
    assert len(failures) == 1
    assert failures[0]["height_span"] == 655
    assert failures[0]["actual_minimum"] == 104
    assert failures[0]["restricted_minimum"] == 115
    corners = [(62, 0), (104, 4), (42, 655), (0, 651)]
    u = (42, 4)
    v = (-62, 651)
    assert sum(x*y for x,y in zip(u,v)) == 0
    assert max(x for x,y in corners)-min(x for x,y in corners) == 104
    assert max(y for x,y in corners)-min(y for x,y in corners) == 655
    print(json.dumps({"heights_checked": [2, 655], "failures": failures,
                      "corners": corners, "status": "passed"}, indent=2))


if __name__ == "__main__":
    main()
