"""Exact four-label mixed-collision certificates for the CRT scaffold.

No search package is required. This verifies canonical representatives,
prime hypotheses, both rectangle presentations, and absence of vertical
P rivals among the four labels. It does not test a filled board.
"""
from itertools import combinations
from math import isqrt
import json
from pathlib import Path


def prime(n):
    if n % 2 == 0:
        return n == 2
    return n > 1 and all(n % d for d in range(3, isqrt(n) + 1, 2))


def crt(a, b, P, Q, p, q):
    aa, bb = P * a * pow(Q, -1, p) % p, P * b * pow(Q, -1, q) % q
    z = aa + ((bb - aa) * pow(p, -1, q) % q) * p
    return z + ((-z) * pow(p * q, -1, 98) % 98) * p * q


def presentation(rect, black):
    return frozenset(set(rect) - black)


def rectangle(points):
    """Independent equal-diagonal test on four distinct integer points."""
    if len(set(points)) != 4:
        return False
    for i in range(1, 4):
        a, c = points[0], points[i]
        b, d = [points[j] for j in range(1, 4) if j != i]
        if (a[0] + c[0], a[1] + c[1]) != (b[0] + d[0], b[1] + d[1]):
            continue
        if sum((a[k] - c[k]) ** 2 for k in (0, 1)) != sum((b[k] - d[k]) ** 2 for k in (0, 1)):
            continue
        if (b[0] - a[0]) * (d[1] - a[1]) != (b[1] - a[1]) * (d[0] - a[0]):
            return True
    return False


def verify(P, Q, p, q, S, ell, y):
    a = 1
    assert prime(p) and prime(q) and p != q
    assert (Q * S) % P == 0
    delta = Q * S // P
    h = a + y + ell * S + delta
    assert p > (P * P + Q * Q) * h
    assert q > (P * P + Q * Q) * h
    labels = [(a, a + y - delta), (a + delta, a + y),
              (a + ell * S, h), (a + ell * S - delta, a + y + ell * S)]
    assert all(1 <= odd <= h and odd % 2 == 1 and
               1 <= even <= h and even % 2 == 0 for odd, even in labels)
    xs = [crt(*label, P, Q, p, q) for label in labels]
    assert len(set(xs)) == 4
    assert [x - xs[0] for x in xs] == [0, S, S - ell * y, -ell * y]
    black = {(x, row) for x, label in zip(xs, labels) for row in label}
    A, B = (xs[0], a), (xs[1], a + y)
    C, D = (xs[2], a + ell * S), (xs[3], a + y + ell * S)
    W1, W2 = (xs[3], a + ell * S), (xs[2], a + y + ell * S)
    tilted = [A, B, W1, W2]
    axis = [C, D, W1, W2]
    assert rectangle(tilted) and rectangle(axis)
    assert set(tilted) != set(axis)
    assert presentation(tilted, black) == presentation(axis, black) == frozenset((W1, W2))
    assert S * (-ell * y) + y * (ell * S) == 0
    assert W1 not in black and W2 not in black
    assert all(1 <= row <= h for _, row in black | {W1, W2})
    # A vertical rival requires an integral alternative of height at most h-1.
    p_rivals = []
    for i, j in combinations(range(4), 2):
        dx = abs(xs[i] - xs[j])
        if dx > h - 1:
            continue
        for ri, rj in ((labels[i][0], labels[j][1]), (labels[i][1], labels[j][0])):
            norm2 = dx * dx + (ri - rj) ** 2
            L = isqrt(norm2)
            if L * L == norm2 and L <= h - 1:
                p_rivals.append((i, j, ri, rj, L))
    assert not p_rivals
    if (P, Q) == (1, 1):
        assert p > 4 * h and q > 4 * h
        assert pow(2, (p - 1) // 2, p) == p - 1
        assert pow(2, (q - 1) // 2, q) == q - 1
    return dict(slope=[P, Q], p=p, q=q, height=h, labels=labels,
                columns=xs, relative_columns=[x-xs[0] for x in xs],
                shared_whites=[W1, W2], tilted=tilted, axis=axis,
                side_norm_squared=S*S+y*y, vertical_rivals=p_rivals, verified=True)


if __name__ == "__main__":
    results = [
        verify(1, 1, 4000291, 4000301, 490, 784, 499547),
        verify(4, 3, 40000463, 40000487, 392, 2450, 532817),
    ]
    out = Path(__file__).with_suffix(".json")
    out.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps([{"slope": r["slope"], "height": r["height"], "verified": True}
                      for r in results]))

