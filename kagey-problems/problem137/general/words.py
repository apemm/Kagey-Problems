"""Run 2 for the general version of Problem 137 (ledger: G5, G9, G10, G11).

Method 1: breadth-first search over the tree of f(x) = x + 1, g(x) = -1/(m x) from 0,
          in exact reduced fractions (written independently of explore.py).
Method 2: enumerate the digit strings (c_1, ..., c_k) allowed by the run rule with q = order of g f,
          evaluate each as f^{c_1} g f^{c_2} g ... g f^{c_k} (0) with Python Fractions,
          and compare values and weights with the BFS ranks point by point.
Method 3: the generating function of the strings, from the run-counter transfer matrix (sympy).

Usage: python words.py m depth     (q is 3, 4, 6 for m = 1, 2, 3)
"""
import sys, time
from fractions import Fraction
from math import gcd
import sympy as sp

QORD = {1: 3, 2: 4, 3: 6}


def bfs(m, depth):
    rank = {(0, 1): 0}
    layer = [(0, 1)]
    counts = [1]
    for n in range(1, depth + 1):
        nxt = []
        for p, d in layer:
            kids = [(p + d, d)]
            if p != 0:
                a, b = -d, m * p
                if b < 0:
                    a, b = -a, -b
                h = gcd(a, b)
                kids.append((a // h, b // h))
            for c in kids:
                if c not in rank:
                    rank[c] = n
                    nxt.append(c)
        layer = nxt
        counts.append(len(layer))
    return rank, counts


def reduced_strings(m, q, D):
    """Yield (value, weight, digits c_1..c_k) for every string allowed by the run rule, weight <= D.

    Weight = c_1 + ... + c_k + k - 1. Rule: c_1 >= 0, c_2..c_k >= 1, no run of q - 2 ones among
    c_2..c_k, except a run starting at c_2 may have length q - 2 when c_1 = 0.
    Also returns a list of strings that would apply g at 0 (should be empty).
    """
    out = []
    poles = []
    for c1 in range(D + 1):                       # k = 1
        out.append((Fraction(c1), c1, (c1,)))
    gm = lambda x: Fraction(-1) / (m * x)
    # stack entries: (x before g, weight so far, trailing run r, digits in application order)
    stack = []
    for ck in range(1, D):                        # first digit c_k, then g
        stack.append((Fraction(ck), ck + 1, 1 if ck == 1 else 0, (ck,)))
    while stack:
        x, w, r, digs = stack.pop()
        if x == 0:
            poles.append(digs)
            continue
        y = gm(x)
        if w > D:
            continue
        # finish with c_1
        if r <= q - 2:
            out.append((y, w, (0,) + digs[::-1]))
        if r <= q - 3:
            for c1 in range(1, D - w + 1):
                out.append((y + c1, w + c1, (c1,) + digs[::-1]))
            for c in range(1, D - w + 1):         # one more interior digit, then g
                nr = r + 1 if c == 1 else 0
                if nr <= q - 2 and w + c + 1 <= D:
                    stack.append((y + c, w + c + 1, nr, digs + (c,)))
    return out, poles


def gf(q):
    t = sp.symbols('t')
    big = t**3 / (1 - t)                         # a digit >= 2 with its g
    one = t**2                                   # a digit 1 with its g
    S = sp.symbols('S0:%d' % (q - 1))            # S_r: trailing run of r ones, r = 0..q-2
    eqs = []
    for r in range(q - 1):
        rhs = 0
        if r == 0:
            rhs += big + big * sum(S[s] for s in range(q - 2))      # from S_0..S_{q-3}
        else:
            rhs += (one if r == 1 else 0) + one * S[r - 1]
        eqs.append(sp.Eq(S[r], rhs))
    sol = sp.solve(eqs, S, dict=True)[0]
    F = 1 / (1 - t) + sum(sol[S[r]] for r in range(q - 2)) / (1 - t) + sol[S[q - 2]]
    F = sp.factor(sp.cancel(sp.together(F)))
    num, den = sp.fraction(sp.cancel(F))
    # normalise so the constant term of the denominator is 1
    c0 = sp.Poly(den, t).eval(0)
    return t, sp.expand(num / c0), sp.expand(den / c0)


def fib(D):
    F = [1, 1]
    while len(F) < D + 1:
        F.append(F[-1] + F[-2])
    return F[:D + 1]


def main():
    if sys.argv[1] == 'gf':
        for q in map(int, sys.argv[2:]):
            t, num, den = gf(q)
            Dq = 1 - t - sum(t**(2 * i + 1) for i in range(1, q - 1))
            Nq = sum(t**(2 * i) for i in range(q - 1)) - t**(2 * q - 3)
            print(f"q={q}: GF {sp.factor(num)} / {sp.factor(den)};  == N_q/D_q: {sp.simplify(num/den - Nq/Dq) == 0}, den == D_q: {sp.expand(den - Dq) == 0}")
        return
    m, D = int(sys.argv[1]), int(sys.argv[2])
    q = QORD.get(m, 10**9)   # m >= 4: g f has infinite order, no run restriction
    t0 = time.time()
    rank, counts = bfs(m, D)
    print(f"m={m} q={q} depth={D}: BFS counts {counts}  ({time.time()-t0:.1f}s)")
    strs, poles = reduced_strings(m, q, D)
    print(f"  {len(strs)} reduced strings of weight <= {D}; strings that hit g(0): {len(poles)} {poles[:5]}  ({time.time()-t0:.1f}s)")
    byval = {}
    for x, w, digs in strs:
        byval.setdefault(x, []).append((w, digs))
    wcounts = [0] * (D + 1)
    for x, w, digs in strs:
        wcounts[w] += 1
    print(f"  string counts by weight {wcounts}")
    print(f"  string counts == BFS counts: {wcounts == counts}")
    dup = {x: v for x, v in byval.items() if len(v) > 1}
    print(f"  values with 2 or more strings: {len(dup)}", sorted(dup.items(), key=lambda kv: min(w for w, _ in kv[1]))[:5])
    wrong = []
    for x, v in byval.items():
        key = (x.numerator, x.denominator)
        if key not in rank or rank[key] != v[0][0]:
            wrong.append((x, v, rank.get(key)))
    print(f"  string values whose weight != BFS rank (or not in BFS): {len(wrong)}", sorted(wrong, key=lambda z: z[1][0][0])[:5])
    missing = [k for k in rank if Fraction(*k) not in byval]
    print(f"  BFS points with no reduced string of weight <= {D}: {len(missing)}", sorted(missing, key=lambda k: rank[k])[:5])
    if q > 50:
        print(f"  free case: counts equal F(n+1): {counts == fib(D)}")
        return
    # generating function
    t, num, den = gf(q)
    Dq = 1 - t - sum(t**(2 * i + 1) for i in range(1, q - 1))
    print(f"  GF numerator {sp.factor(num)}   denominator {sp.factor(den)}")
    print(f"  denominator == D_q: {sp.expand(den - Dq) == 0}")
    ser = sp.Poly(sp.series(num / den, t, 0, D + 41).removeO(), t)
    coeffs = [int(ser.coeff_monomial(t**i)) for i in range(D + 41)]
    print(f"  GF coefficients 0..{D}: match BFS: {coeffs[:D+1] == counts}")
    print(f"  GF coefficients {D+1}..{D+40}: {coeffs[D+1:]}")
    # fit with the preregistered denominator D_q: numerator from the first terms only
    e = 2 * q - 3
    A = sum(counts[i] * t**i for i in range(e + 1))
    prod = sp.Poly(sp.expand(A * Dq), t)
    N_fit = sum(prod.coeff_monomial(t**i) * t**i for i in range(e + 1))
    ser2 = sp.Poly(sp.series(N_fit / Dq, t, 0, D + 1).removeO(), t)
    pred = [int(ser2.coeff_monomial(t**i)) for i in range(D + 1)]
    print(f"  fit with denominator D_q on terms 0..{e}: numerator {sp.expand(N_fit)}; "
          f"matches the {D - e} further BFS terms {e+1}..{D}: {pred == counts}")
    # blind Pade fit: smallest (d, d) whose fit on the first 2d+1 terms matches all later BFS terms
    for d in range(1, 12):
        if 2 * d + 1 > D + 1:
            break
        # solve for denominator 1 + b_1 t + ... + b_d t^d so that coefficients d+1..2d of A*B vanish
        b = sp.symbols('b1:%d' % (d + 1))
        eq = [counts[n] + sum(b[j - 1] * counts[n - j] for j in range(1, d + 1)) for n in range(d + 1, 2 * d + 1)]
        s = sp.solve(eq, b, dict=True)
        if not s:
            continue
        s = s[0]
        if len(s) < d:
            continue
        B = [1] + [s[b[j]] for j in range(d)]
        ok = all(counts[n] + sum(B[j] * counts[n - j] for j in range(1, d + 1)) == 0 for n in range(d + 1, D + 1))
        if ok:
            Bpoly = sp.factor(sum(B[j] * t**j for j in range(d + 1)))
            print(f"  blind Pade: first (d,d) consistent with all BFS terms is d={d}, fitted on terms 0..{2*d}, "
                  f"checked on {D - 2*d} further terms; denominator {Bpoly}")
            break
    print(f"  total time {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
