"""Exact independent DP checks for adjacent-bin equality and global extrema."""
from fractions import Fraction as F
from math import isqrt


def pmf(n, p):
    left, right = [F(1, 2), F(0)], [F(0), F(1, 2)]
    q = 1 - p
    for size in range(2, n + 1):
        a, b = [F(0)] * (size + 1), [F(0)] * (size + 1)
        for k in range(size):
            a[k] += p * left[k] + q * right[k]
            b[k + 1] += q * left[k] + p * right[k]
        left, right = a, b
    return [a + b for a, b in zip(left, right)]


count = 0
for n in range(2, 81):
    for p in (F(1, 10), F(1, 3), F(1, 2), F(2, 3), F(9, 10), F(99, 100)):
        row = pmf(n, p)
        u = (1 - p) / p
        ratio = 2 * u + (n - 2) * u * u
        assert row[1] == row[0] * ratio
        assert row[1] == min(row[1:-1])
        assert row[n // 2] == max(row[1:-1])
        assert min(row) == (row[0] if ratio >= 1 else row[1])
        assert max(row) == max(row[0], row[n // 2])
        count += 1
    s = isqrt(n - 1)
    if s * s == n - 1:
        p = F(1 + s, 2 + s)
        row = pmf(n, p)
        assert row[0] == row[1] == min(row)
print(f'PASS: adjacent polynomial and global extrema in {count} exact distributions;')
print('PASS: exact equality at all square-root-rational thresholds through N=80.')
