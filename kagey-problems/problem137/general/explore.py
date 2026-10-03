"""First checks for the general version of Problem 137 (see data/ledger.md, G1 to G8)."""
import sys
from fractions import Fraction
from itertools import product

def bfs(m, depth):
    rank = {(0, 1): 0}
    frontier = [(0, 1)]
    counts = [1]
    tag = {}
    both = 0
    for n in range(depth):
        new = {}
        for (p, q) in frontier:
            c = (p + q, q)
            if c not in rank:
                new[c] = new.get(c, '') + 'f'
            if p:
                num, den = -q, m * p
                if den < 0: num, den = -num, -den
                from math import gcd
                g_ = gcd(abs(num), den)
                c = (num // g_, den // g_)
                if c not in rank:
                    new[c] = new.get(c, '') + 'g'
        for c, t in new.items():
            rank[c] = n + 1
            tag[c] = ''.join(sorted(set(t)))
            if len(tag[c]) == 2: both += 1
        frontier = list(new)
        counts.append(len(frontier))
    return rank, tag, counts, both

def check_rec(counts, lags, lo):
    bad = [n for n in range(max(lags), len(counts)) if counts[n] != sum(counts[n - l] for l in lags)]
    return bad

for m, depth in ((1, 22), (2, 28), (3, 26), (4, 24), (5, 22), (6, 22)):
    rank, tag, counts, both = bfs(m, depth)
    print(f"m={m}: counts {counts}")
    if m == 1: print("  rec lags 1,3 fails at", check_rec(counts, (1, 3), 4))
    if m == 2: print("  rec lags 1,3,5 fails at", check_rec(counts, (1, 3, 5), 8))
    if m == 3: print("  rec lags 1,3,5,7,9 fails at", check_rec(counts, (1, 3, 5, 7, 9), 12))
    if m >= 4:
        fib = [1, 1]
        while len(fib) < len(counts): fib.append(fib[-1] + fib[-2])
        print("  equals F(n+1):", counts == fib[:len(counts)], " lags 1,2 fails at", check_rec(counts, (1, 2), 2))
    # colors
    neg_not_g = [c for c, t in tag.items() if (c[0] < 0) != ('g' in t)]
    print(f"  reached by both f and g at its rank: {both}; color/sign mismatches: {len(neg_not_g)} {neg_not_g[:5]}")
    # reachability by the parent map
    if m <= 4:
        fails = []
        for q in range(1, 61):
            for p in range(-60, 61):
                x = Fraction(p, q); seen = 0
                while x != 0 and seen < 5000:
                    x = x - 1 if x > 0 else Fraction(-1, 1) / (m * x)
                    seen += 1
                if x != 0: fails.append(Fraction(p, q))
        print(f"  parent map fails to reach 0 from {len(set(fails))} of the rationals with |p|,q<=60; first {sorted(set(fails), key=lambda z:(z.denominator,abs(z.numerator)))[:6]}")
    if m in (1, 2, 3):
        qord = {1: 3, 2: 4, 3: 6}[m]
        # parent-map step count vs rank
        bad = 0
        for c, r in rank.items():
            x = Fraction(*c); s = 0
            while x != 0 and s <= r + 2:
                x = x - 1 if x > 0 else Fraction(-1, 1) / (m * x); s += 1
            if x != 0 or s != r: bad += 1
        print(f"  parent-map steps differ from rank at {bad} of {len(rank)} points")
