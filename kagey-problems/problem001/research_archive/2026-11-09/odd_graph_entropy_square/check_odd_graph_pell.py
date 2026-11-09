"""Check the anchored congruence-neighbor construction with exact integers."""

import json


def return_period(modulus):
    x, y = 1, 1
    period = 0
    while True:
        x, y = (9*x+20*y) % modulus, (4*x+9*y) % modulus
        period += 1
        if (x, y) == (1, 1):
            return period
        assert period <= modulus*modulus


def main():
    clique_witnesses = [(5, 11, 13), (15, 5, 25), (33, 5, 65),
                        (15, 11, 17), (33, 11, 55), (15, 33, 39)]
    for u, v, hyp in clique_witnesses:
        assert u*u+4*(v-u)**2 == hyp*hyp
    assert len({frozenset((u,v)) for u,v,_ in clique_witnesses}) == 6
    rows = []
    tests = 0
    for m in range(1, 33):
        period = return_period(10*m)
        x, y = 1, 1
        for _ in range(period):
            x, y = 9*x+20*y, 4*x+9*y
        assert x*x-5*y*y == -4
        assert (x-1) % (10*m) == (y-1) % (10*m) == 0
        z = (x+4)//5
        assert z > 1 and z % 2 == 1 and (z-1) % (2*m) == 0
        assert z*z+4*(z-1)**2 == y*y
        for v in (-101, -7, -1, 1, 3, 55, 101):
            w = z*v
            assert w != v and (w-v) % m == 0 and w % 2 == 1
            assert w*w+4*(v-w)**2 == (v*y)**2
            tests += 1
        rows.append({"modulus": m, "return_power": period,
                     "multiplier_decimal_digits": len(str(z))})
    print(json.dumps({"anchor_checks": tests, "K4": clique_witnesses, "moduli": rows,
                      "status": "passed"}, indent=2))


if __name__ == "__main__":
    main()
