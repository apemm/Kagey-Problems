"""Independent exact checks of the d-direction occupation-count formula.

Uses only the Python standard library. Run directly.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product
from math import comb, factorial, prod


def compositions(n, d):
    if d == 1:
        yield (n,)
    else:
        for k in range(n + 1):
            for tail in compositions(n - k, d - 1):
                yield (k,) + tail


def exact(k, p):
    n, d = sum(k), len(k)
    if not n:
        return F(1)
    r = (1 - p) / (d - 1)
    sigma = p - r
    total = F(0)
    for m in product(*(range(1, a + 1) if a else (0,) for a in k)):
        M = sum(m)
        coefficient = factorial(M) // prod(factorial(b) for b in m)
        coefficient *= prod(comb(a - 1, b - 1) for a, b in zip(k, m) if a)
        total += coefficient * r ** (M - 1) * sigma ** (n - M)
    return total / d


def dp(n, d, p):
    if not n:
        return {(0,) * d: F(1)}
    states = {}
    for a in range(d):
        k = tuple(int(i == a) for i in range(d))
        states[k, a] = F(1, d)
    for _ in range(1, n):
        nxt = defaultdict(F)
        for (k, a), weight in states.items():
            for b in range(d):
                new_k = tuple(v + int(i == b) for i, v in enumerate(k))
                nxt[new_k, b] += weight * (p if a == b else (1 - p) / (d - 1))
        states = nxt
    result = defaultdict(F)
    for (k, a), weight in states.items():
        result[k] += weight
    return dict(result)


def enumerate_words(n, d, p):
    if not n:
        return {(0,) * d: F(1)}
    result = defaultdict(F)
    for word in product(range(d), repeat=n):
        k = tuple(word.count(i) for i in range(d))
        weight = F(1, d)
        for a, b in zip(word, word[1:]):
            weight *= p if a == b else (1 - p) / (d - 1)
        result[k] += weight
    return dict(result)


def check():
    cells = distributions = word_rows = 0
    for d, limit, enum_limit in [(2, 14, 9), (3, 11, 7), (4, 8, 5)]:
        values = sorted({F(0), F(1, 10), F(1, d), F(1, 2), F(2, 3), F(9, 10), F(1)})
        for p in values:
            for n in range(limit + 1):
                predicted = {k: exact(k, p) for k in compositions(n, d)}
                computed = dp(n, d, p)
                assert predicted == computed, (d, n, p)
                assert sum(predicted.values()) == 1
                assert all(v >= 0 for v in predicted.values())
                if n <= enum_limit:
                    assert predicted == enumerate_words(n, d, p), (d, n, p)
                    word_rows += 1
                means = [sum(k[a] * v for k, v in predicted.items()) for a in range(d)]
                assert means == [F(n, d)] * d
                sigma = (d * p - 1) / (d - 1)
                inflation = n * n if p == 1 else n * (1 + sigma) / (1 - sigma) - 2 * sigma * (1 - sigma**n) / (1 - sigma)**2
                for a in range(d):
                    for b in range(d):
                        cov = sum((k[a] - means[a]) * (k[b] - means[b]) * v for k, v in predicted.items())
                        assert cov == (F(int(a == b), d) - F(1, d*d)) * inflation
                cells += len(predicted)
                distributions += 1
    print(f'PASS: {cells} exact bin probabilities in {distributions} distributions agree with independent DP.')
    print(f'PASS: {word_rows} distributions also agree with independent exhaustive word enumeration.')
    print('PASS: all means, covariance entries, normalization, nonnegativity, and boundary values.')


if __name__ == '__main__':
    check()
