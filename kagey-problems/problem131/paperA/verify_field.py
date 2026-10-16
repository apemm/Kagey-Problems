"""A magnetic field (Theorem 5.9 and the values quoted after it).

For the fields B = 0.1, 0.2, 0.3, 0.5 the script computes the limits y_a(B), the roots of
H_a(y) = e^(2Ba) with H_a of (eq:edge-polynomial), their minimum y_*(B) over a >= 2 and the
minimizing a. It checks part (c) of the theorem on a grid of fields on both sides of (1/2) log 2,
and the bound H_a(1/t) t^a <= (t + 1/2)^(a-1) used in its proof. For N = 10^4 it finds the exact
crossings u^(a)_N of the free and periodic chains from the run polynomials (verify_allbin.ratio,
verify_periodic_window.periodic_ratio) and reports N (min_{a>=2} u^(a)_N)^2. It asserts every
value quoted in Section 5 to the digits shown there.

Only the standard library is required. Run with python -B in this folder (a few seconds).
"""
from decimal import Decimal as D, getcontext
import math

from verify_allbin import ratio
from verify_periodic_window import periodic_ratio

getcontext().prec = 40
AMAX = 60

QUOTED = {  # B: (minimizing a, y_*, exact periodic at 10^4, exact free at 10^4)
    0.1: (11, '0.757', '0.758', '0.741'),
    0.2: (4, '1.287', '1.288', '1.266'),
    0.3: (2, '1.764', '1.764', '1.738'),
    0.5: (2, '2.972', '2.973', '2.939'),
}


def H(a, y):
    return sum(math.comb(a - 1, r) * y ** (r + 1) / math.factorial(r + 1) for r in range(a))


def logH(a, y):
    """log H_a(y) without overflow."""
    ts = [math.log(math.comb(a - 1, r)) + (r + 1) * math.log(y) - math.lgamma(r + 2) for r in range(a)]
    m = max(ts)
    return m + math.log(math.fsum(math.exp(t - m) for t in ts))


def bisect(f, lo, hi, n=200):
    for _ in range(n):
        m = (lo + hi) / 2
        if f(m) < 0:
            lo = m
        else:
            hi = m
    return (lo + hi) / 2


def tail_start(B, Y):
    """Smallest A with 4 sqrt(Y) exp(2 sqrt(Y a) - 2 B a) < 1 for every a >= A (proof of (b))."""
    a = 1
    while True:
        g = lambda t: math.log(4 * math.sqrt(Y)) + 2 * math.sqrt(Y * t) - 2 * B * t
        # g is concave in t, so once it is negative and decreasing it stays negative
        if g(a) < 0 and g(a + 1) < g(a):
            return a
        a += 1


def limits(B):
    a_max = AMAX
    while True:
        ys = {a: bisect(lambda y: logH(a, y) - 2 * B * a, 1e-12, 1e4) for a in range(1, a_max)}
        a_star = min(range(2, a_max), key=lambda a: ys[a])
        A = tail_start(B, ys[a_star] + 1)
        if A <= a_max:
            return ys, a_star  # every a >= A has y_a > y_* + 1, so the minimum is global
        a_max = A + 1


def exact_min(B, N, law, amax=30):
    best = None
    for a in range(2, amax):
        b, s = N - a, math.sqrt(a * (N - a))
        def g(t):
            return float(law(a, b, D(math.sqrt(t / N) * s))) * math.exp(-2 * B * a) - 1
        t = bisect(g, 0.0, 400.0, 120)
        best = t if best is None else min(best, t)
    return best


def main():
    for B, (a_q, y_q, per_q, free_q) in QUOTED.items():
        ys, a_star = limits(B)
        per = exact_min(B, 10**4, periodic_ratio)
        free = exact_min(B, 10**4, ratio)
        print(f'B={B}: y_1={ys[1]:.4f}, y_*={ys[a_star]:.4f} at a={a_star}; N=10^4 periodic {per:.4f}, free {free:.4f}')
        assert a_star == a_q and f'{ys[a_star]:.3f}' == y_q, B
        assert f'{per:.3f}' == per_q and f'{free:.3f}' == free_q, B
    half_log2 = 0.5 * math.log(2)
    for B in [0.05 * k for k in range(1, 21)]:
        ys, a_star = limits(B)
        if B > half_log2 + 1e-9:
            assert ys[a_star] > math.exp(2 * B), B
        elif B < half_log2 - 1e-9:
            assert ys[a_star] < math.exp(2 * B), B
    for t in [0.1, 0.3, 0.5]:
        for a in range(2, 30):
            assert H(a, 1 / t) * t ** a <= (t + 0.5) ** (a - 1) * (1 + 1e-12), (t, a)
    ys, _ = limits(half_log2)
    assert abs(ys[2] - 2) < 1e-9 and abs(ys[1] - 2) < 1e-9
    print('All checks passed.')


if __name__ == '__main__':
    main()
