"""Exact root isolation for the factors of the four-row denominator Q4.

Reads the irreducible factors of Q4 from jis/data/four_row_recurrence.json, isolates every
real and complex root of each factor in rational intervals or rectangles (SymPy, exact
arithmetic), and checks which roots can have modulus below R = 341/1000. A root counts as
inside when its whole isolating box lies in the open disk of radius R, and as ambiguous when
the box meets the circle. The expected result: the only root inside is the positive root of
the degree-20 factor (1/rho_4 = 0.29832...), and no root is ambiguous.
Output: jis/data/four_row_root_isolation.json.
"""
import json
import os
import time

import sympy
from sympy import Poly, Rational, im, re, symbols, sympify

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, '..', 'data')
R = Rational(341, 1000)


def main():
    z = symbols('z')
    rec = json.load(open(os.path.join(DATA, 'four_row_recurrence.json')))
    out = {'radius': '341/1000', 'sympy_version': sympy.__version__, 'factors': []}
    t0 = time.time()
    for f in rec['factors']:
        g = Poly(sympify(f['factor']), z)
        real_iv, cx_iv = g.intervals(all=True, eps=Rational(1, 10**6))
        inside, ambiguous = [], []
        for (a, b), _ in real_iv:
            lo = 0 if a * b <= 0 else min(abs(a), abs(b))
            hi = max(abs(a), abs(b))
            if hi < R:
                inside.append([str(a), str(b)])
            elif lo <= R:
                ambiguous.append([str(a), str(b)])
        for (p1, p2), _ in cx_iv:
            x1, y1, x2, y2 = re(p1), im(p1), re(p2), im(p2)
            xm = 0 if x1 <= 0 <= x2 else min(abs(x1), abs(x2))
            ym = 0 if y1 <= 0 <= y2 else min(abs(y1), abs(y2))
            if xm ** 2 + ym ** 2 <= R ** 2:
                ambiguous.append([str(p1), str(p2)])
        out['factors'].append({'factor': f['factor'], 'degree': g.degree(),
                               'multiplicity': f['multiplicity'],
                               'roots_inside': inside, 'ambiguous': ambiguous})
        print(g.degree(), f['multiplicity'], len(inside), len(ambiguous), flush=True)
    out['seconds'] = round(time.time() - t0, 1)
    out['only_root_inside_is_dominant'] = (
        sum(len(x['roots_inside']) for x in out['factors']) == 1
        and all(not x['ambiguous'] for x in out['factors']))
    with open(os.path.join(DATA, 'four_row_root_isolation.json'), 'w') as fh:
        json.dump(out, fh, indent=1)
    print(out['only_root_inside_is_dominant'], out['seconds'])


if __name__ == '__main__':
    main()
