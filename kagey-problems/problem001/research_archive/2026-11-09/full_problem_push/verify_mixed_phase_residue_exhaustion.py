"""Exhaust the necessary 2-adic residue patterns of generic circle orbits."""
from fractions import Fraction
from itertools import product
from pathlib import Path
import json
import time


def q(value):
    return value * (value - 1) // 2 % 2


def density_numerators(points):
    # Numerators over eight, from all translated base points modulo four.
    x0, y0 = points[0]
    diffs = [(x-x0, y-y0) for x, y in points[1:]]
    ordinary = 4 * all(y % 2 == 0 for x, y in diffs)
    checker = 4 * all((x+y) % 2 == 0 for x, y in diffs)
    quadratic = sum(all((q(x)+q(y)+u*x+v*y) % 2 == 0
                        for x, y in diffs)
                    for u, v in product(range(2), repeat=2))
    return ordinary, checker, quadratic


def main():
    started = time.monotonic()
    expected = {
        ('OO', 0): ('0', '1/4', '1/8'),
        ('OO', 1): ('1/4', '1/2', '1/4'),
        ('OO', 2): ('1/4', '1/2', '3/8'),
        ('OE', 0): ('1/4', '0', '1/8'),
        ('OE', 1): ('1/4', '1/4', '0'),
        ('OE', 2): ('1/4', '1/4', '1/4'),
        ('EO', 0): ('0', '0', '1/8'),
        ('EO', 1): ('1/4', '1/4', '0'),
        ('EO', 2): ('1/2', '1/4', '1/4'),
    }
    checked = 0
    by_type = {}
    for a, b in product(range(8), repeat=2):
        if a % 2 == b % 2 == 0:
            continue
        kind = 'OO' if a % 2 and b % 2 else ('OE' if a % 2 else 'EO')
        for odd_scale in (1, 3, 5, 7):
            target = odd_scale**2 * (a*a+b*b) % 16
            for wx, wy in product(range(8), repeat=2):
                if (wx*wx+wy*wy) % 16 != target:
                    continue
                # Keep all eight orbit operations, including repeated residues.
                # A generic actual orbit has eight members even when residues repeat.
                orbit = [(sx*x, sy*y)
                         for x, y in ((wx, wy), (wy, wx))
                         for sx, sy in product((-1, 1), repeat=2)]
                for valuation in (0, 1, 2, 3):
                    factor = 2**valuation
                    ux, uy = factor*odd_scale*a, factor*odd_scale*b
                    counts = [0, 0, 0]
                    samples = 0
                    compatible = 0
                    for x, y in orbit:
                        vx, vy = factor*x, factor*y
                        if (ux+vx) % 2 or (uy+vy) % 2:
                            continue
                        compatible += 1
                        for ell in range(4):
                            tx, ty = -ell*b, ell*a
                            points = [(tx, ty), (tx+ux, ty+uy),
                                      ((ux+vx)//2, (uy+vy)//2),
                                      ((ux-vx)//2, (uy-vy)//2)]
                            values = density_numerators(points)
                            counts = [u+v for u, v in zip(counts, values)]
                            samples += 1
                    actual = tuple(str(Fraction(c, 8*samples)) for c in counts)
                    assert actual == expected[kind, min(valuation, 2)], (
                        a, b, odd_scale, wx, wy, valuation, actual)
                    assert compatible == (4 if valuation == 0 and kind != 'OO' else 8)
                    checked += 1
                    key = f'{kind}:v={valuation}'
                    by_type[key] = by_type.get(key, 0) + 1
    result = dict(status='PASS', checked=checked, by_type=by_type,
                  scope='All necessary modulo-16 norm patterns, primitive modulo two; generic orbit operations retain multiplicity',
                  seconds=time.monotonic()-started)
    dest = Path(__file__).with_suffix('.json')
    dest.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
