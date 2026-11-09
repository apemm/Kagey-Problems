"""Affine edge orders for a row-1 sea with doubles every 4th column (even h, parity partition).
Edge (i, j) <-> rows {2i+1, 2j+2}, i, j in Z_n, n = h/2. Slot k = n t + r gets
i = (A r + B t + E) mod n, j = (C r + D t + F) mod n, with AD - BC a unit mod n.
Counts violations whose four corners lie between the first and last double columns.
Usage: python affine_orders.py h [spacing]"""
import sys
from math import gcd
from itertools import product
from fastcheck import violations


def interior_violations(h, cols, lo, hi):
    v, det = violations(h, cols, detail=True)
    return sum(1 for kind, cs, P in det if all(lo <= x <= hi for x, _ in cs))


def main():
    h = int(sys.argv[1]); sp = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    n = h // 2
    best = []
    for A, B, C, D in product(range(n), repeat=4):
        if gcd((A * D - B * C) % n, n) != 1:
            continue
        for E, F in ((0, 0),):
            order = []
            for k in range(n * n):
                t, r = divmod(k, n)
                order.append((2 * ((A * r + B * t + E) % n) + 1, 2 * ((C * r + D * t + F) % n) + 2))
            if len(set(order)) != n * n:
                continue
            cols = [{1}] * 3
            for idx, e in enumerate(order):
                if idx:
                    cols += [{1}] * (sp - 1)
                cols.append(set(e))
            cols += [{1}] * 3
            lo, hi = 3, 3 + sp * (n * n - 1)
            iv = interior_violations(h, cols, lo, hi)
            best.append((iv, (A, B, C, D)))
    best.sort()
    print('h', h, 'spacing', sp, 'orders tried', len(best), 'fewest interior violations', best[:8], flush=True)


if __name__ == '__main__':
    main()
