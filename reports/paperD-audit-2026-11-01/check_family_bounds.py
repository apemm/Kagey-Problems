"""Independent finite-grid checks for Appendix A and the family identities.

The Polya lower comparison is checked in exact rational arithmetic using
backward transition recursions. The upper factor is only a floating-point
stress test; the manuscript proof supplies the bound for all parameters.
"""
from fractions import Fraction as F
from math import comb, exp, lgamma, log
import json


def hitting(n, step):
    rows = {n: [F(int(b == n // 2)) for b in range(n + 1)]}
    for s in range(n - 1, 0, -1):
        rows[s] = [(1 - step(s, b)) * rows[s + 1][b]
                   + step(s, b) * rows[s + 1][b + 1]
                   for b in range(s + 1)]
    return rows


def log_phi(n, s, b, c):
    h = n // 2
    if not 0 <= h - b <= n - s:
        return float('-inf')
    return (log(comb(n - s, h - b)) + 2 * lgamma(h + c)
            - lgamma(n + 2 * c) - lgamma(b + c)
            - lgamma(s - b + c) + lgamma(s + 2 * c))


comparisons = 0
jensen_checks = 0
for n in range(2, 25, 2):
    for eps in (F(1, 100), F(1, 10), F(6, 25), F(49, 100)):
        actual = hitting(n, lambda s, b: eps + (1 - 2 * eps) * F(b, s))
        jensen = float(4 * eps / (n + 2)) * (1 - float(eps)) ** (2 - 12 / (n + 4))
        assert float(actual[1][0]) + 1e-14 >= jensen, (n, eps, jensen)
        jensen_checks += 1
        alpha = eps / (1 - 2 * eps)
        for s in range(2, n + 1):
            for c in (F(0), alpha * s / 2, alpha * s):
                urn = hitting(n, lambda u, b: (b + c) / (u + 2 * c))
                for b in range(1, s):
                    assert actual[s][b] >= urn[s][b], (n, eps, s, b, c)
                    comparisons += 1

upper_checks = 0
max_excess = float('-inf')
for n in (4, 8, 16, 32, 64, 128):
    for eps in (0.0001, 0.01, 0.1, 0.24):
        kap = 2 * eps / (1 - 4 * eps)
        for s in range(2, n):
            c, cp = kap * (s + 10), kap * (s + 11)
            sigma = s + 2 * c
            for b in range(max(1, s - n // 2), min(n // 2, s - 1) + 1):
                r = eps + (1 - 2 * eps) * b / s
                base = log_phi(n, s, b, c)
                delta = ((1 - r) * exp(log_phi(n, s + 1, b, cp) - base)
                         + r * exp(log_phi(n, s + 1, b + 1, cp) - base))
                excess = log(delta) - kap / sigma - 2 * kap / (3 * sigma**2)
                assert excess < 1e-9, (n, eps, s, b, excess)
                max_excess = max(max_excess, excess)
                upper_checks += 1

family_checks = 0
for n in range(2, 80):
    for d in range(1, n):
        betas = [F(comb(n - d - 1, v - 2), comb(n - 1, v - 1))
                 if v - 2 <= n - d - 1 else F(0) for v in range(2, n + 1)]
        assert sum(betas) == F(n, d * (d + 1))
        assert sum((v - 2) * z for v, z in zip(range(2, n + 1), betas)) == F(
            2 * n * (n - d - 1), d * (d + 1) * (d + 2))
        family_checks += 1

print(json.dumps({
    'exact_polya_comparisons': comparisons,
    'jensen_center_checks': jensen_checks,
    'upper_factor_float_checks': upper_checks,
    'largest_upper_factor_excess': max_excess,
    'exact_family_identity_pairs': family_checks,
    'status': 'passed',
    'scope': 'finite grid only; does not replace proof or kernel checks'
}, indent=2))
