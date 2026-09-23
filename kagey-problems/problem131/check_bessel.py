"""Independent decimal-arithmetic check of the uniform Bessel bound and roots.

No third-party dependencies. This is numerical corroboration, not the proof.
"""
from decimal import Decimal as D, localcontext
from math import log, pi


def exact_polynomial(n, x):
    h = D(n) / 2
    u = x / h
    a, b = n // 2, (n + 1) // 2
    term, total = D(1), D(0)
    for r in range(a):
        total += term * (2 * u + u * u * D(n - 2 - 2 * r) / (r + 1))
        ratio = D((a - 1 - r) * (b - 1 - r)) * u * u / (r + 1) ** 2
        term *= ratio
        # Once decreasing, every later ratio is smaller; this cutoff puts
        # omitted relative mass far below the displayed precision.
        if ratio < D('0.5') and abs(term) < abs(total) * D('1e-65'):
            break
    return total


def bessel_f(x):
    term, total = D(1), D(0)
    for r in range(10000):
        total += term * (1 + x / (r + 1))
        term *= x * x / (r + 1) ** 2
        if r > 2 * x and term < total * D('1e-65'):
            return 2 * x * total
    raise RuntimeError('series did not converge')


def bisect(f, target, hi):
    lo = D(0)
    for _ in range(240):
        mid = (lo + hi) / 2
        if f(mid) < target:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


with localcontext() as ctx:
    ctx.prec = 80
    checked = 0
    for n in range(2, 202):
        h = D(n) / 2
        for x in map(D, ['0.01', '0.2', '0.5', '1', '2', '4', '8']):
            b = bessel_f(x) / h
            s = exact_polynomial(n, x)
            error = 1 - s / b
            assert error >= -D('1e-60'), (n, x, error)
            assert error <= x * (x + 1) / h + D('1e-60'), (n, x, error)
            checked += 1
    print(f'Uniform inequality passed at {checked} even/odd grid points.')
    print('N, p_N, u_B/u_N, x_N-x_B, root_bound, leading_residual, refined_residual')
    for n in [100, 101, 400, 401, 800, 1600, 3200, 10000, 1000000, 100000000]:
        h = D(n) / 2
        hi = D(str(log(n) + 3))
        xn = bisect(lambda x: exact_polynomial(n, x), D(1), hi)
        xb = bisect(bessel_f, h, hi)
        delta = xn * (xn + 1) / h
        bound = -(1 - delta).ln() / 2
        assert 0 <= xn - xb <= bound
        p = 1 / (1 + xn / h)
        l = D(n).ln()
        c = (D(str(pi)) / 8).ln() / 2
        leading = l - l.ln() / 2 + c
        refined = leading + (l.ln() / 4 - c / 2 + D(1) / 8) / l
        print(f'{n}, {p:.12f}, {xb/xn:.12f}, {xn-xb:.8g}, {bound:.8g}, '
              f'{D(n)*(1-p)-leading:.8g}, {D(n)*(1-p)-refined:.8g}')
