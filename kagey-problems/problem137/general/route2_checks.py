"""Run R2 for the general version of Problem 137 (ledger: R2-1 to R2-4).

Checks of the hand proofs in data/proofs_route2.md.
R2-1: d(x - 1) = d(x) + 2q - 3 for x < 0, by BFS rank and by the parent-algorithm string weight.
R2-2: the height ht(p/q) = q^2 / gcd(q, m) and its drop along the parent sequence.
R2-3: the free case m >= 4 stays in the predicted intervals.
R2-4: psi_q, C_q, the other roots of D_q, and |a(n) - C_q psi_q^n| < 1.

Usage: python route2_checks.py
"""
import math
from fractions import Fraction
from math import gcd, ceil

import mpmath as mp
import numpy as np

from words import bfs

QORD = {2: 4, 3: 6}


def string_of(x, m):
    """Digits (c_1, ..., c_k) from the parent algorithm, using x alone (no BFS)."""
    if x == 0:
        return (0,)
    if x < 0:
        return (0,) + string_of(Fraction(-1) / (m * x), m)
    digs = []
    while True:
        c = ceil(x)
        digs.append(c)
        if x == c:
            return tuple(digs)
        x = Fraction(1) / (m * (c - x))


def weight(s):
    return sum(s) + len(s) - 1


def ht(x, m):
    return Fraction(x.denominator ** 2, gcd(x.denominator, m))


def r2_1():
    for m, depth in ((2, 28), (3, 26)):
        q = QORD[m]
        rank, _ = bfs(m, depth)
        jump = 2 * q - 3
        n_chk = bad = 0
        for (p, d), r in rank.items():
            if p < 0 and r <= depth - jump:
                x = Fraction(p, d)
                y = x - 1
                r_bfs = rank.get((y.numerator, y.denominator))
                w_x, w_y = weight(string_of(x, m)), weight(string_of(y, m))
                n_chk += 1
                if r_bfs != r + jump or w_y != w_x + jump or w_x != r:
                    bad += 1
        print(f"R2-1 m={m}: checked {n_chk} negative x of rank <= {depth - jump}, failures {bad}")


def r2_2():
    N = 200
    for m in (2, 3, 4, 5):
        bad = 0
        for den in range(1, N + 1):
            for num in range(-N, N + 1):
                if num == 0 or gcd(num, den) != 1:
                    continue
                x = Fraction(num, den)
                if ht(x + 1, m) != ht(x, m) or ht(Fraction(-1) / (m * x), m) != m * x * x * ht(x, m):
                    bad += 1
        print(f"R2-2 m={m}: height identities on |p|, q <= {N}: failures {bad}")
    for m in (2, 3):
        q = QORD[m]
        bad_drop = bad_run = 0
        maxrun = {True: 0, False: 0}
        for den in range(1, N + 1):
            for num in range(-N, N + 1):
                if num == 0 or gcd(num, den) != 1:
                    continue
                x = Fraction(num, den)
                start_neg = x < 0
                hts = [] if start_neg else [ht(x, m)]
                run, first_flip, first_run = 0, True, True
                steps = 0
                while x != 0:
                    steps += 1
                    if x > 0:
                        x -= 1
                        continue
                    y = Fraction(-1) / (m * x)
                    c = ceil(y)
                    if c == 1:
                        run += 1
                    else:
                        limit = q - 2 if (start_neg and first_run) else q - 3
                        maxrun[start_neg and first_run] = max(maxrun[start_neg and first_run], run)
                        if run > limit:
                            bad_run += 1
                        run, first_run = 0, False
                        if not (start_neg and first_flip):
                            hts.append(ht(y, m))
                    first_flip = False
                    x = y
                limit = q - 2 if (start_neg and first_run) else q - 3
                maxrun[start_neg and first_run] = max(maxrun[start_neg and first_run], run)
                if run > limit:
                    bad_run += 1
                if any(hts[i + 1] >= hts[i] for i in range(len(hts) - 1)):
                    bad_drop += 1
        print(f"R2-2 m={m}: drop failures {bad_drop}, run failures {bad_run}, "
              f"longest closed run (first run from x<0: {maxrun[True]}, other: {maxrun[False]})")


def r2_3():
    for m in (4, 5, 6):
        rank, _ = bfs(m, 22)
        out = 0
        for (p, d) in rank:
            x = Fraction(p, d)
            if x < 0 and not (Fraction(-2, m) < x):
                out += 1
            if x > 0 and not (ceil(x) - Fraction(2, m) < x):
                out += 1
        has = [(v.numerator, v.denominator) in rank for v in (Fraction(-1), Fraction(1, 2))]
        print(f"R2-3 m={m}: {len(rank)} points, outside the intervals {out}, -1 present {has[0]}, 1/2 present {has[1]}")


def r2_4():
    mp.mp.dps = 40
    for m, q, depth in ((2, 4, 28), (3, 6, 30)):
        _, counts = bfs(m, depth)
        D = [1, -1] + [0] * (2 * q - 4)
        for j in range(3, 2 * q - 2, 2):
            D[j] = -1
        Dp = lambda t: mp.mpf(1) - t - sum(t ** j for j in range(3, 2 * q - 2, 2))
        dDp = lambda t: -1 - sum(j * t ** (j - 1) for j in range(3, 2 * q - 2, 2))
        Rq = lambda t: sum(t ** (2 * i) for i in range(q - 2))
        t0 = mp.findroot(Dp, 0.6)
        psi = 1 / t0
        C = (1 + t0) * Rq(t0) / (-dDp(t0))
        roots = np.roots(D[::-1])
        mods = sorted(abs(r) for r in roots)
        others = [r for r in roots if abs(r - float(t0)) > 1e-9]
        rho = min(abs(r) for r in others)
        lo = 15 if m == 2 else 20
        errs = [abs(counts[n] - C * psi ** n) for n in range(lo, depth + 1)]
        print(f"R2-4 q={q}: t0 = {mp.nstr(t0, 15)}, psi = {mp.nstr(psi, 15)}, C = {mp.nstr(C, 15)}, "
              f"blue share 1/(1+psi) = {mp.nstr(1 / (1 + psi), 10)}")
        print(f"      root moduli {[round(float(x), 6) for x in mods]}; smallest other modulus {rho:.6f} "
              f"(> t0: {rho > float(t0)}); max |a(n) - C psi^n| for {lo} <= n <= {depth}: {mp.nstr(max(errs), 6)}")


if __name__ == '__main__':
    r2_1()
    r2_2()
    r2_3()
    r2_4()
