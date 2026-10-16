"""Targeted interval checks for the fixed-field result (Theorem 5.9).

Run with python -B verify_field.py. Only the standard library is required.
For each of the four quoted fields, enclose the candidate minimum by outward
interval signs, compare every other bin below a certified cutoff, and exclude
ALL remaining bins using the theorem's tail bound. No field grid is swept.
The finite minima are global, including bins beyond N/2.

All positive polynomials are evaluated in full, without truncation. Exact
enumeration and rational threshold checks give independent checks. Arithmetic
comes from certified_decimal.py. These examples do not replace the proof for
all fields. The endpoint brackets also certify the quoted rounding.
"""
from decimal import Decimal as D, localcontext
from fractions import Fraction as F
from itertools import product
from math import comb, factorial

from certified_decimal import Interval as I, PRECISION

# B: (minimizing a, limiting y_*, periodic N u^2, free N u^2 at N=10^4)
QUOTED = {
    '0.1': (11, '0.757', '0.758', '0.741'),
    '0.2': (4, '1.287', '1.288', '1.266'),
    '0.3': (2, '1.764', '1.764', '1.738'),
    '0.5': (2, '2.972', '2.973', '2.939'),
}


def sqrt_interval(value):
    """Widen nearest-rounded square roots, then certify endpoints by squaring."""
    value = I.coerce(value)
    if value.lo < 0:
        raise ValueError('Square root needs a nonnegative interval')
    with localcontext() as ctx:
        ctx.prec = PRECISION
        lo = D(0) if value.lo == 0 else ctx.next_minus(value.lo.sqrt())
        hi = D(0) if value.hi == 0 else ctx.next_plus(value.hi.sqrt())
    assert (I(lo) ** 2).hi <= value.lo
    assert (I(hi) ** 2).lo >= value.hi
    return I(lo, hi)


def zero_field(a, y, N=None, boundary=None):
    """Enclose H_a(y), or the finite run polynomial at u=sqrt(y/N)."""
    y = I.coerce(y)
    if N is None:
        if a < 1:
            raise ValueError('H_a needs a positive index')
        term, total = y, I(0)
        for r in range(a):
            total += term
            if r + 1 < a:
                term *= y * I.rational(a - 1 - r, (r + 1) * (r + 2))
        return total
    if not 1 <= a < N or boundary not in ('free', 'periodic'):
        raise ValueError('Need an interior bin and a boundary condition')
    b, u2 = N - a, y / N
    u = sqrt_interval(u2) if boundary == 'free' else None
    term, total = I(1), I(0)
    for r in range(min(a, b)):
        if boundary == 'free':
            total += term * (2 * u + I.rational(N - 2 - 2 * r, r + 1) * u2)
        else:
            total += term * I.rational(N, r + 1) * u2
        if r + 1 < min(a, b):
            term *= u2 * I.rational((a - 1 - r) * (b - 1 - r), (r + 1) ** 2)
    return total


def root_bracket(value):
    """Certify a root to width 1e-12 by endpoint signs and monotonicity."""
    with localcontext() as ctx:
        ctx.prec = PRECISION
        lo, hi = D(0), D(4)
        while value(hi).lo <= 1:
            hi *= 2
        while hi - lo > D('1e-12'):
            mid = (lo + hi) / 2
            sign = value(mid)
            if sign.hi < 1:
                lo = mid
            elif sign.lo > 1:
                hi = mid
            else:
                raise ArithmeticError('Interval sign is undecided')
    assert value(lo).hi < 1 < value(hi).lo
    return I(lo, hi)


def tail_cutoff(B, Y):
    """Certify the tail for all N, both boundaries and the limiting polynomial.

    The theorem gives R <= 4 sqrt(Y) exp(2 sqrt(Y a) - 2 B a).
    Use 4 sqrt(Y) <= 2(Y+1) and 2 sqrt(Y a) <= B a + Y/B.
    This logarithmic upper bound decreases linearly with a.
    """
    B, Y = I(B), I(Y)
    intercept = (2 * (Y + 1)).ln() + Y / B
    A = max(3, int((intercept / B).hi) + 1)
    assert (intercept - B * A).hi < 0
    return A


def certify_minimum(B, a_star, quoted, N=None, boundary=None):
    """Certify the minimizing index and quoted rounding, including the tail."""
    factors = {}

    def value(a, y):
        if a not in factors:
            factors[a] = (-2 * I(B) * a).exp()
        return zero_field(a, y, N, boundary) * factors[a]

    bracket = root_bracket(lambda y: value(a_star, y))
    with localcontext() as ctx:
        ctx.prec = PRECISION
        center = D(quoted)
        assert center - D('0.0005') < bracket.lo < bracket.hi < center + D('0.0005')
    A = tail_cutoff(B, bracket.hi)
    stop = A if N is None else min(A, N)
    assert 2 <= a_star < stop
    for a in range(2, stop):
        if a != a_star:
            assert value(a, bracket.hi).hi < 1, (B, N, boundary, a)
    label = 'limit' if N is None else f'N={N} {boundary}'
    print(f'B={B} {label}: y in [{bracket.lo}, {bracket.hi}], '
          f'global minimizer a={a_star}, tail a>={A}', flush=True)
    return bracket


def check_enumeration():
    """Compare finite evaluators with exact word weights, independently."""
    count, u = 0, F(1, 4)
    for N in range(2, 10):
        totals = {law: [F(0) for _ in range(N + 1)] for law in ('free', 'periodic')}
        for word in product((0, 1), repeat=N):
            a = sum(word)
            walls = sum(word[j] != word[j + 1] for j in range(N - 1))
            totals['free'][a] += u ** walls
            totals['periodic'][a] += u ** (walls + (word[-1] != word[0]))
        for boundary in totals:
            for a in range(1, N):
                actual = zero_field(a, I.rational(N, 16), N, boundary)
                assert F(actual.lo) <= totals[boundary][a] <= F(actual.hi)
                count += 1
    for a in range(1, 21):
        y = F(3, 4)
        exact = sum(F(comb(a - 1, r), factorial(r + 1)) * y ** (r + 1)
                    for r in range(a))
        actual = zero_field(a, I.rational(3, 4))
        assert F(actual.lo) <= exact <= F(actual.hi)
    print(f'Independent enumeration: {count} finite-bin checks passed; '
          '20 limiting polynomials checked exactly.', flush=True)


def check_threshold():
    """Exact examples of the factorial bound, equality and both sides."""
    for t in (F(1, 10), F(3, 10), F(1, 2), F(3, 4)):
        for a in range(2, 65):
            value = sum(F(comb(a - 1, r), factorial(r + 1)) * t ** (a - 1 - r)
                        for r in range(a))
            assert value <= (t + F(1, 2)) ** (a - 1)
            if t < F(1, 2):
                assert value < 1
            elif t == F(1, 2):
                assert value <= 1 and (value == 1) == (a == 2)
            elif a == 2:
                assert value > 1
    # Direct check of the periodic triple tie. At the one-spin crossing,
    # t=e^(-2B), y=1/t and R_2=t+(N-3)/(2N). Its critical t -> 1/2.
    for N in (4, 5, 10, 100, 10000):
        t = F(N + 3, 2 * N)
        assert t + F(N - 3, 2 * N) == 1
        for a in (1, 2):
            actual = (zero_field(a, I.rational(t.denominator, t.numerator),
                                 N, 'periodic')
                      * I.rational(t.numerator, t.denominator) ** a)
            assert actual.lo <= 1 <= actual.hi
    print('Exact rational threshold checks passed below, at and above B_c, '
          'including the periodic finite-N triple tie.', flush=True)


def main():
    check_enumeration()
    check_threshold()
    for B, (a_star, limit_q, periodic_q, free_q) in QUOTED.items():
        limiting = certify_minimum(B, a_star, limit_q)
        one_spin = (2 * I(B)).exp()
        if B in ('0.1', '0.2', '0.3'):
            assert limiting.hi < one_spin.lo
        else:
            assert limiting.lo > one_spin.hi
        certify_minimum(B, a_star, periodic_q, 10000, 'periodic')
        certify_minimum(B, a_star, free_q, 10000, 'free')
    print('All targeted field checks passed. No field-grid sweep was run.')


if __name__ == '__main__':
    main()
