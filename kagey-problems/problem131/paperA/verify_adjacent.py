"""Exact independent DP checks for adjacent-bin equality and global extrema."""
from fractions import Fraction as F
from math import isqrt
from itertools import product


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

# Obtain the central crossing polynomial directly from words, independently
# of the closed run-count formula used in the proof.
for n in range(2, 13):
    a, b = n // 2, n - n // 2
    coefficients = [0] * n
    for word in product((0, 1), repeat=n):
        if sum(word) == a:
            changes = sum(x != y for x, y in zip(word, word[1:]))
            coefficients[changes] += 1
    assert coefficients[0] == 0 and coefficients[1] == 2
    if n >= 3:
        assert coefficients[2] == n - 2
    if n >= 4:
        assert coefficients[3] == 2 * (a - 1) * (b - 1) > 0
        assert all(c >= 0 for c in coefficients[3:])
        # S_N strictly exceeds the adjacent polynomial at every positive odds.
        for u in (F(1, 100), F(1, 3), F(1), F(2)):
            assert sum(c * u**j for j, c in enumerate(coefficients)) > 2*u + (n-2)*u*u
        # At p=0 there are additional zero-probability endpoint/adjacent ties.
        row = pmf(n, F(0))
        assert row[0] == row[1] == 0
    else:
        assert all(c == 0 for c in coefficients[3:])
print('PASS: central/adjacent strict coefficient gap and N=2,3 ties by word enumeration through N=12.')
