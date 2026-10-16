"""Second method for the couplings of Table 3: the transfer matrix.

verify_ising_coupling.py finds the central crossings from the run polynomials. This script
finds them again from the 2 x 2 transfer matrix of the Ising chain, with no run counting.
With a fugacity x per up spin and a weight u per domain wall,
    T(x) = [[x, u], [x u, 1]]     (rows: spin i, columns: spin i+1, index 0 = up),
the periodic chain has generating polynomial Tr T(x)^N and the free chain
(x, 1) T(x)^(N-1) (1, 1)^T. Both have coefficient 1 at x^N (the all-up configuration), so
the coefficient of x^(N/2) (of x^(floor(N/2)) for odd N) is the ratio of the middle bin to
an endpoint. We extract it exactly as a discrete Fourier sum over the M = N + 1 roots of
unity, which has no aliasing since the degree is N, and evaluate T(x)^n by repeated
squaring in double precision. The crossing is the root of this ratio minus 1 in log u.

The script compares J = -(1/2) log u with the values in data/ising-coupling-verification.json
written by verify_ising_coupling.py, and asserts agreement within 1e-7.

Needs NumPy. Run with python -B in this folder. Run time is about two minutes.
"""
import json
import math
from pathlib import Path

import numpy as np

NS = [10, 20, 50, 100, 1000, 10**4, 10**5, 10**6]
TOL = 1e-7


def mat_pow(x, u, n):
    """Entries (a, b, c, d) of T(x)^n, elementwise over the array x."""
    one = np.ones_like(x)
    ra, rb, rc, rd = one, np.zeros_like(x), np.zeros_like(x), one
    a, b, c, d = x, u * one, x * u, one
    while n:
        if n & 1:
            ra, rb, rc, rd = ra * a + rb * c, ra * b + rb * d, rc * a + rd * c, rc * b + rd * d
        n >>= 1
        if n:
            a, b, c, d = a * a + b * c, a * b + b * d, c * a + d * c, c * b + d * d
    return ra, rb, rc, rd


def middle_ratio(n, u, periodic):
    m = n + 1
    j = np.arange(m)
    x = np.exp(2j * math.pi * j / m)
    if periodic:
        a, _, _, d = mat_pow(x, u, n)
        f = a + d
    else:
        a, b, c, d = mat_pow(x, u, n - 1)
        f = x * (a + b) + (c + d)
    k = n // 2
    coeff = np.sum(f * np.exp(-2j * math.pi * j * k / m)) / m
    return coeff.real


def crossing_odds(n, periodic):
    """Root of middle_ratio = 1 by bisection in log u."""
    g = lambda t: middle_ratio(n, math.exp(t), periodic) - 1
    lo = hi = math.log(math.log(n) / n)
    while g(lo) > 0:
        lo -= 0.5
    while g(hi) < 0:
        hi += 0.5
    for _ in range(45):
        mid = (lo + hi) / 2
        if g(mid) < 0:
            lo = mid
        else:
            hi = mid
    return math.exp((lo + hi) / 2)


def main():
    here = Path(__file__).parent
    ref = json.loads((here / 'data' / 'ising-coupling-verification.json').read_text())['rows']
    # sanity check against exact small cases: S_4 = 2u + 2u^2 + 2u^3, S^P_{4,2} = 4u^2 + 2u^4
    for u in (0.1, 0.3):
        assert abs(middle_ratio(4, u, False) - (2*u + 2*u**2 + 2*u**3)) < 1e-12
        assert abs(middle_ratio(4, u, True) - (4*u**2 + 2*u**4)) < 1e-12
    print(f'{"N":>8} {"J^P transfer":>14} {"J^P runs":>12} {"J^F transfer":>14} {"J^F runs":>12}')
    worst = 0.0
    for n in NS:
        jp = -0.5 * math.log(crossing_odds(n, True))
        jf = -0.5 * math.log(crossing_odds(n, False))
        rp, rf = float(ref[str(n)]['J_periodic']), float(ref[str(n)]['J_free'])
        worst = max(worst, abs(jp - rp), abs(jf - rf))
        print(f'{n:>8} {jp:14.9f} {rp:12.9f} {jf:14.9f} {rf:12.9f}')
        assert abs(jp - rp) < TOL and abs(jf - rf) < TOL, n
    print(f'Largest difference {worst:.2e}. All checks passed.')


if __name__ == '__main__':
    main()
