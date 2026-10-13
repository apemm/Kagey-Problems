"""Exact check: the 'fresh or repeat the last' walk has the Polya urn law.

Walk on d states. At step t = 1, 2, ..., T: with probability d*th/(d*th + t - 1)
draw a fresh uniform state, otherwise repeat the previous state. Claim:
P(counts = m, last state = j) = DM(m; th,...,th) * m_j / T, where DM is the
Dirichlet-multinomial law (Polya urn with mass th on each colour).
At th = 1 this is the aging walk of Paper D after its first step.
"""
from fractions import Fraction as Fr
from itertools import product
from math import factorial


def walk_law(d, th, T):
    law = {}
    # state: (counts tuple, last)
    cur = {}
    for j in range(d):
        m = [0] * d
        m[j] = 1
        cur[(tuple(m), j)] = Fr(1, d)
    for t in range(2, T + 1):
        fresh = d * th / (d * th + t - 1)
        nxt = {}
        for (m, last), p in cur.items():
            for j in range(d):
                q = fresh / d + ((1 - fresh) if j == last else 0)
                mm = list(m)
                mm[j] += 1
                key = (tuple(mm), j)
                nxt[key] = nxt.get(key, 0) + p * q
        cur = nxt
    return cur


def rising(x, n):
    r = Fr(1)
    for i in range(n):
        r *= x + i
    return r


def dm(m, th):
    T = sum(m)
    d = len(m)
    r = Fr(factorial(T)) / rising(d * th, T)
    for mj in m:
        r *= rising(th, mj) / factorial(mj)
    return r


ok = True
for d in (2, 3, 4):
    for th in (Fr(1), Fr(1, 2), Fr(2), Fr(3, 7)):
        for T in range(1, 8 if d < 4 else 6):
            law = walk_law(d, th, T)
            for (m, j), p in law.items():
                if p != dm(m, th) * m[j] / T:
                    ok = False
                    print("MISMATCH", d, th, T, m, j)
print("fresh-or-repeat walk equals the Polya urn law (counts and last state):", ok)

# Paper D's walk at theta = 1: X_1 = 1, at step k >= 2 stay w.p. (k-1)/(k+d-2).
ok2 = True
for d in (2, 3, 4):
    for N in range(2, 8):
        cur = {((1,) + (0,) * (d - 1), 0): Fr(1)}
        for k in range(2, N + 1):
            nxt = {}
            for (n, last), p in cur.items():
                for j in range(d):
                    q = Fr(k - 1, k + d - 2) if j == last else Fr(1, k + d - 2)
                    nn = list(n)
                    nn[j] += 1
                    nxt[(tuple(nn), j)] = nxt.get((tuple(nn), j), 0) + p * q
            cur = nxt
        urn = walk_law(d, Fr(1), N - 1)
        for (n, j), p in cur.items():
            m = (n[0] - 1,) + n[1:]
            if urn.get((m, j), 0) != p:
                ok2 = False
print("Paper D walk at theta = 1 is the same walk after one step:", ok2)
if not (ok and ok2):
    raise SystemExit(1)
