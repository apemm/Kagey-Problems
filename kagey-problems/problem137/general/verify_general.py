"""Checks for "Trees of rationals from x -> x + 1 and an involution" (Problem 137, general version).

Every number printed in the paper is recomputed here by two independent methods.

  Method 1 (BFS).      Breadth-first search from 0 over the tree of f and g, in exact arithmetic.
  Method 2 (words).    Enumeration of the reduced digit strings of Theorem B_q (run rule), each
                       evaluated as f^{c_1} g f^{c_2} g ... g f^{c_k}(0), compared point by point.
  Method 3 (formula).  The series of N_q/D_q, an integer recurrence, and for the generating function
                       itself a symbolic transfer matrix (sympy) that does not use the closed form.
  Method 4 (parent).   The parent map, run from the value alone, with no BFS.

Cases: m = 1, 2, 3 (q = 3, 4, 6) in x-coordinates with Python Fractions, q = 5 in X-coordinates
with exact arithmetic in Q(sqrt 5), and the free case m = 4, 5, 6.

Usage: python verify_general.py          (about one minute and under 2 GB of memory)
"""
import sys
import time
from fractions import Fraction as Fr
from math import gcd

import mpmath as mp
import sympy as sp

FAIL = []


def check(name, ok, detail=""):
    print(f"  [{'ok' if ok else 'FAIL'}] {name}" + (f"  {detail}" if detail else ""))
    if not ok:
        FAIL.append(name)


# ----------------------------------------------------------------------------------------------
# Two kinds of trees. Each has: zero, F (add lambda), G (the involution), sign, neg_lambda.
# ----------------------------------------------------------------------------------------------

class RatTree:
    """f(x) = x + 1, g(x) = -1/(m x) on Q (x-coordinates)."""

    def __init__(self, m):
        self.m = m
        self.zero = Fr(0)
        self.one = Fr(1)

    def F(self, x, c=1):
        return x + c

    def G(self, x):
        return Fr(-1) / (self.m * x)

    def sign(self, x):
        return (x > 0) - (x < 0)


def q5_sign(x):
    a, b = x
    if a >= 0 and b >= 0:
        return 0 if (a == 0 and b == 0) else 1
    if a <= 0 and b <= 0:
        return -1
    if a > 0:
        return 1 if a * a > 5 * b * b else -1
    return 1 if 5 * b * b > a * a else -1


class Q5Tree:
    """F(X) = X + lambda, G(X) = -1/X with lambda = 2 cos(pi/5) = (1 + sqrt 5)/2."""
    LAM = (Fr(1, 2), Fr(1, 2))

    def __init__(self):
        self.zero = (Fr(0), Fr(0))
        self.one = self.LAM

    def F(self, x, c=1):
        return (x[0] + c * self.LAM[0], x[1] + c * self.LAM[1])

    def G(self, x):
        a, b = x
        n = a * a - 5 * b * b
        return (-a / n, b / n)

    def sign(self, x):
        return q5_sign(x)


# ----------------------------------------------------------------------------------------------
# Method 1: BFS
# ----------------------------------------------------------------------------------------------

def bfs(T, depth):
    """Return rank dict, counts, and for each point the list of (parent, move) at rank - 1."""
    rank = {T.zero: 0}
    how = {T.zero: []}
    layer = [T.zero]
    counts = [1]
    for n in range(1, depth + 1):
        nxt = []
        for x in layer:
            kids = [(T.F(x), 'f')]
            if x != T.zero:
                kids.append((T.G(x), 'g'))
            for y, mv in kids:
                r = rank.get(y)
                if r is None:
                    rank[y] = n
                    how[y] = [mv]
                    nxt.append(y)
                elif r == n:
                    how[y].append(mv)
        layer = nxt
        counts.append(len(layer))
    return rank, how, counts


# ----------------------------------------------------------------------------------------------
# Method 2: reduced strings
# ----------------------------------------------------------------------------------------------

def reduced_strings(T, q, D):
    """All reduced strings (Theorem B_q) of weight <= D, as (value, weight, digits c_1..c_k).

    q = None means no run restriction (the free case). Raises if g would be applied at 0.
    The word f^{c_1} g f^{c_2} g ... g f^{c_k} acts right to left on 0, so c_k comes first.
    """
    cap = 10 ** 9 if q is None else q - 3          # longest allowed run of interior 1's
    out = [(T.F(T.zero, c1), c1, (c1,)) for c1 in range(D + 1)]
    # state: tail value Y = [c_j..c_k], weight of c_j..c_k with their g's, left run r, digits
    stack = [(T.F(T.zero, c), c + 1, 1 if c == 1 else 0, (c,)) for c in range(1, D)]
    while stack:
        y, w, r, digs = stack.pop()
        if w > D:
            continue
        if y == T.zero:
            raise AssertionError(f"g applied at 0 by {digs}")
        gy = T.G(y)
        # close with c_1 = 0: a run of length cap + 1 = q - 2 at c_2 is allowed
        if r <= cap + 1:
            out.append((gy, w, (0,) + digs[::-1]))
        if r <= cap:
            for c1 in range(1, D - w + 1):
                out.append((T.F(gy, c1), w + c1, (c1,) + digs[::-1]))
        # one more interior digit c_j, then its g
        for c in range(1, D - w):
            nr = r + 1 if c == 1 else 0
            if r > cap or nr > cap + 1:
                continue
            stack.append((T.F(gy, c), w + c + 1, nr, digs + (c,)))
    return out


# ----------------------------------------------------------------------------------------------
# Method 3: the series of N_q/D_q, and the symbolic transfer matrix
# ----------------------------------------------------------------------------------------------

def Dq_coeffs(q):
    if q is None:
        return [1, -1, -1]
    c = [0] * (2 * q - 2)
    c[0] = 1
    c[1] = -1
    for j in range(3, 2 * q - 2, 2):
        c[j] = -1
    return c


def Nq_coeffs(q):
    if q is None:
        return [1]
    c = [0] * (2 * q - 2)
    for j in range(0, 2 * q - 3, 2):
        c[j] = 1
    c[2 * q - 3] = -1
    return c


def series(num, den, n):
    a = []
    for k in range(n + 1):
        s = num[k] if k < len(num) else 0
        for j in range(1, len(den)):
            if k - j >= 0:
                s -= den[j] * a[k - j]
        a.append(s)
    return a


def transfer_matrix_gf(q):
    """GF of the reduced strings from a run-counter automaton, without using N_q/D_q."""
    t = sp.symbols('t')
    big, one = t ** 3 / (1 - t), t ** 2
    S = sp.symbols('S0:%d' % (q - 1))      # S_r: c_j..c_k read so far, left run of r ones
    eqs = []
    for r in range(q - 1):
        if r == 0:
            rhs = big + big * sum(S[s] for s in range(q - 2))
        else:
            rhs = (one if r == 1 else 0) + one * S[r - 1]
        eqs.append(sp.Eq(S[r], rhs))
    sol = sp.solve(eqs, S, dict=True)[0]
    Fgf = 1 / (1 - t) + sum(sol[S[r]] for r in range(q - 2)) / (1 - t) + sol[S[q - 2]]
    num, den = sp.fraction(sp.cancel(sp.together(Fgf)))
    c0 = sp.Poly(den, t).eval(0)
    return t, sp.expand(num / c0), sp.expand(den / c0)


# ----------------------------------------------------------------------------------------------
# Method 4: the parent map
# ----------------------------------------------------------------------------------------------

def parent_digits(T, x, limit=10 ** 5):
    """Run P from x. Return (steps, digit string of x if x > 0) or (None, None) if no 0 in limit."""
    steps = 0
    digs = []
    run = 0
    while x != T.zero:
        if T.sign(x) > 0:
            x = T.F(x, -1)
            run += 1
        else:
            x = T.G(x)
            digs.append(run)
            run = 0
        steps += 1
        if steps > limit:
            return None, None
    digs.append(run)
    return steps, tuple(digs)


# ----------------------------------------------------------------------------------------------

def tree_checks(name, T, q, D, extra_rank=None):
    t0 = time.time()
    print(f"\n== {name}, q = {q if q else 'infinity'}, ranks 0..{D}")
    rank, how, counts = bfs(T, D)
    print(f"  BFS counts {counts}")
    print(f"  {len(rank)} points  ({time.time() - t0:.1f}s)")
    strs = reduced_strings(T, q, D)
    wc = [0] * (D + 1)
    seen = {}
    coll = 0
    for v, w, d in strs:
        wc[w] += 1
        if v in seen:
            coll += 1
        seen[v] = (w, d)
    check("string counts equal BFS counts", wc == counts)
    check("no two reduced strings share a value", coll == 0)
    check("every string weight equals the BFS rank of its value",
          all(rank.get(v) == w for v, w, _ in strs))
    check("every BFS point has a reduced string", all(x in seen for x in rank))
    ser = series(Nq_coeffs(q), Dq_coeffs(q), D)
    check("counts equal the series of N_q/D_q" if q else "counts equal F(n+1)", ser == counts)
    if q:
        bad = [n for n in range(2 * q - 3, D + 1)
               if counts[n] - counts[n - 1] - sum(counts[n - j] for j in range(3, 2 * q - 2, 2)) != 0]
        n0 = 2 * q - 3
        defect = counts[n0] - counts[n0 - 1] - sum(counts[n0 - j] for j in range(3, 2 * q - 2, 2))
        check(f"recurrence with lags 1, 3, ..., {2 * q - 3} holds for {2 * q - 2} <= n <= {D}, "
              f"defect at n = {n0} is -1", bad == [n0] and defect == -1, f"fails at {bad}")
    # colors and the tree property
    nonzero = [x for x in rank if x != T.zero]
    check("each point is reached at its rank by exactly one edge (rows have no repeats)",
          all(len(how[x]) == 1 for x in nonzero))
    check("reached by g iff negative",
          all((how[x][0] == 'g') == (T.sign(x) < 0) for x in nonzero))
    # parent map: steps = rank, digit string = reduced string (method 4, no BFS)
    okp = okd = True
    for x, r in rank.items():
        st, dg = parent_digits(T, x)
        okp &= (st == r)
        if T.sign(x) > 0:
            okd &= (seen[x][1] == dg)
    check("parent map reaches 0 in exactly d(x) steps at every point", okp)
    check("digits read off the parent map equal the reduced string (positive points)", okd)
    # positives r(n), negatives = r(n - 1)
    rpos = [0] * (D + 1)
    for x, r in rank.items():
        if T.sign(x) > 0:
            rpos[r] += 1
    check("a(n) = r(n) + r(n - 1) for n >= 1",
          all(counts[n] == rpos[n] + rpos[n - 1] for n in range(1, D + 1)))
    # jump 2q - 3 (x < -lambda, both ranks in range); in x coordinates X < -lambda is x < -1
    if q:
        J = 2 * q - 3
        jumps = [(x, rank[x], rank.get(T.F(x))) for x in rank
                 if T.sign(x) < 0 and T.sign(T.F(x)) < 0]
        check(f"d(x + 1) = d(x) - {J} for every x < -1 in range",
              all(r1 == r - J for x, r, r1 in jumps), f"({len(jumps)} points)")
        # d(-lambda) = 2q - 4
        check(f"d(-1) = 2q - 4 = {2 * q - 4}", rank.get(T.F(T.zero, -1)) == 2 * q - 4)
    print(f"  ({time.time() - t0:.1f}s)")
    return rank, how, counts, rpos


def main():
    T0 = time.time()
    results = {}
    for m, q, D in [(1, 3, 24), (2, 4, 28), (3, 6, 30)]:
        results[m] = tree_checks(f"m = {m}", RatTree(m), q, D)
    results['q5'] = tree_checks("q = 5 in Q(sqrt 5)", Q5Tree(), 5, 20)
    for m in (4, 5, 6):
        results[m] = tree_checks(f"m = {m} (free)", RatTree(m), None, 22)

    # ------------------------------------------------------------------ free case intervals
    print("\n== free case: where the points are (Theorem E, parts (a) and (e) of the free-case theorem)")
    for m in (4, 5, 6):
        rank = results[m][0]
        ok = True
        for x in rank:
            if x < 0:
                ok &= (-Fr(2, m) < x < 0)
            elif x > 0:
                c = -((-x.numerator) // x.denominator)       # ceiling
                ok &= (c - Fr(2, m) < x <= c)
        check(f"m = {m}: negatives in (-2/m, 0), positives in (c - 2/m, c]", ok)
        check(f"m = {m}: -1 and 1/2 not reached", Fr(-1) not in rank and Fr(1, 2) not in rank)
    T4 = RatTree(4)
    x, seq = Fr(1, 2), []
    for _ in range(4):
        seq.append(x)
        x = x - 1 if x > 0 else T4.G(x)
    check("m = 4: parent map cycles 1/2, -1/2, 1/2, ...", seq == [Fr(1, 2), Fr(-1, 2)] * 2)

    # ------------------------------------------------------------------ reachability
    print("\n== reachability (Theorem D), all p/r with |p|, r <= 60")
    for m in (1, 2, 3, 4):
        T = RatTree(m)
        pts = {Fr(p, r) for p in range(-60, 61) for r in range(1, 61)}
        fails = sum(1 for x in pts if parent_digits(T, x, 10 ** 4)[0] is None)
        if m <= 3:
            check(f"m = {m}: parent map reaches 0 from all {len(pts)} rationals", fails == 0)
        else:
            check("m = 4: parent map fails from 3726 of them", fails == 3726, f"({fails})")
    print("  height h(p/r) = r^2/gcd(r, m): h(x + 1) = h(x), h(g_m x) = m x^2 h(x), |p|, r <= 200")
    for m in (1, 2, 3):
        ok = True
        for p in range(-200, 201):
            for r in range(1, 201):
                if p == 0 or gcd(p, r) != 1:
                    continue
                x = Fr(p, r)
                h = lambda z: Fr(z.denominator ** 2, gcd(z.denominator, m))
                ok &= h(x + 1) == h(x) and h(RatTree(m).G(x)) == m * x * x * h(x)
        check(f"m = {m}: height identities", ok)

    # ------------------------------------------------------------------ examples in the paper
    print("\n== examples in the paper")
    r2 = results[2][0]
    T2 = RatTree(2)
    check("m = 2: d(1/2) = 3, digits (1, 1)",
          r2[Fr(1, 2)] == 3 and parent_digits(T2, Fr(1, 2)) == (3, (1, 1)))
    check("m = 2: d(3/5) = 11, digits (1, 2, 1, 2, 1)",
          r2[Fr(3, 5)] == 11 and parent_digits(T2, Fr(3, 5)) == (11, (1, 2, 1, 2, 1)))
    # 3/5 = 1 - 1/(2*2 - 1/(1 - 1/(2*2 - 1/1)))
    val = 1 - 1 / (4 - 1 / (1 - 1 / (4 - Fr(1))))
    check("m = 2: 1 - 1/(4 - 1/(1 - 1/(4 - 1))) = 3/5", val == Fr(3, 5))
    want = [{Fr(0)}, {Fr(1)}, {Fr(2), Fr(-1, 2)}, {Fr(3), Fr(-1, 4), Fr(1, 2)},
            {Fr(4), Fr(-1, 6), Fr(3, 4), Fr(3, 2), Fr(-1)},
            {Fr(5), Fr(-1, 8), Fr(5, 6), Fr(7, 4), Fr(-2, 3), Fr(5, 2), Fr(-1, 3)}]
    got = [{x for x, r in r2.items() if r == n} for n in range(6)]
    check("m = 2: ranks 0..5 as in Table 2 (the hand table of the 2-tree)", got == want)
    st, dg = parent_digits(T2, Fr(-3, 2))
    print(f"  m = 2: d(-3/2) = {r2[Fr(-3, 2)]} (parent map {st}), d(-1/2) = {r2[Fr(-1, 2)]}")
    check("m = 2: d(-3/2) = d(-1/2) + 5", r2[Fr(-3, 2)] == r2[Fr(-1, 2)] + 5)
    check("figure: m = 1 tree to rank 7 has 31 vertices, m = 2 has 48",
          sum(results[1][2][:8]) == 31 and sum(results[2][2][:8]) == 48)

    # Table 4 of the paper (n = 0..20), checked against the BFS counts
    tab4 = {1: [1, 1, 2, 2, 3, 5, 7, 10, 15, 22, 32, 47, 69, 101, 148, 217, 318, 466, 683, 1001, 1467],
            2: [1, 1, 2, 3, 5, 7, 11, 18, 28, 44, 69, 108, 170, 267, 419, 658, 1033, 1622, 2547, 3999, 6279],
            'q5': [1, 1, 2, 3, 5, 8, 13, 20, 32, 52, 83, 133, 213, 341, 546, 874, 1400, 2242, 3590, 5749, 9206],
            3: [1, 1, 2, 3, 5, 8, 13, 21, 34, 54, 87, 141, 227, 366, 590, 951, 1533, 2471, 3983, 6420, 10349],
            4: [1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597, 2584, 4181, 6765, 10946]}
    check("Table 4 equals the BFS counts", all(results[k][2][:21] == v for k, v in tab4.items()))

    # ------------------------------------------------------------------ OEIS A060961
    print("\n== OEIS A060961 (offset 0, terms copied from the entry)")
    A060961 = [1, 1, 1, 2, 3, 5, 8, 12, 19, 30, 47, 74, 116, 182, 286, 449, 705, 1107, 1738, 2729, 4285]
    a = lambda j: A060961[j] if j >= 0 else 0
    rpos2 = results[2][3]
    check("m = 2: r(n) = A060961(n-1) + A060961(n-3) for 1 <= n <= 21",
          all(rpos2[n] == a(n - 1) + a(n - 3) for n in range(1, 22)))
    check("A060961 terms equal the series of 1/D_4", series([1], Dq_coeffs(4), 20) == A060961)

    # ------------------------------------------------------------------ generating functions
    print("\n== generating functions, symbolic transfer matrix (q = 3..8)")
    for q in range(3, 9):
        t, num, den = transfer_matrix_gf(q)
        Dq = sum(c * t ** j for j, c in enumerate(Dq_coeffs(q)))
        Nq = sum(c * t ** j for j, c in enumerate(Nq_coeffs(q)))
        g = sp.gcd(sp.Poly(Nq, t), sp.Poly(Dq, t))
        check(f"q = {q}: transfer matrix gives N_q/D_q, denominator exactly D_q, gcd(N_q, D_q) = 1",
              sp.expand(den - Dq) == 0 and sp.expand(num - Nq) == 0 and g.degree() == 0)

    # ------------------------------------------------------------------ growth constants
    print("\n== growth constants (Proposition growth), 40 digits")
    mp.mp.dps = 40
    ROUND_N0 = {3: 3, 4: 6, 6: 11}  # thresholds stated in Remark nearest
    table = {}
    for q in (3, 4, 5, 6, None):
        Dc, Nc = Dq_coeffs(q), Nq_coeffs(q)
        Dp = lambda x: sum(c * x ** j for j, c in enumerate(Dc))
        Np = lambda x: sum(c * x ** j for j, c in enumerate(Nc))
        dDp = lambda x: sum(j * c * x ** (j - 1) for j, c in enumerate(Dc) if j)
        # positives have g.f. t R_q / D_q, and t / (1 - t - t^2) in the free case
        Rp = (lambda x: sum(x ** (2 * i) for i in range(q - 2))) if q else (lambda x: 1)
        t0 = mp.findroot(Dp, mp.mpf('0.65'))
        psi = 1 / t0
        C1 = -Np(t0) / (t0 * dDp(t0))                          # residue
        C2 = (1 + t0) * Rp(t0) / (-dDp(t0))                     # closed form, Proposition growth
        roots = mp.polyroots(Dc[::-1], maxsteps=200, extraprec=200)
        others = sorted(abs(z) for z in roots if abs(z - t0) > mp.mpf(10) ** -20)
        ser = series(Nc, Dc, 400)
        ratio = mp.mpf(ser[400]) / ser[399]
        Cn = mp.mpf(ser[400]) / psi ** 400
        nearest = all(int(mp.nint(C1 * psi ** n)) == ser[n] for n in range(1, 81))
        lab = q if q else 'inf'
        print(f"  q = {lab}: psi = {mp.nstr(psi, 12)}, C = {mp.nstr(C1, 12)}, "
              f"1/(1 + psi) = {mp.nstr(1 / (1 + psi), 10)}, other |roots| >= {mp.nstr(others[0], 8)}")
        check(f"q = {lab}: two formulas for C agree, and a(400)/psi^400 agrees",
              abs(C1 - C2) < mp.mpf(10) ** -30 and abs(Cn - C1) < mp.mpf(10) ** -20)
        check(f"q = {lab}: a(400)/a(399) agrees with psi", abs(ratio - psi) < mp.mpf(10) ** -20)
        check(f"q = {lab}: every other root of D_q has modulus > 1", others[0] > 1)
        check(f"q = {lab}: a(n) = nearest integer to C psi^n for 1 <= n <= 80", nearest)
        if q in (3, 4, 6):  # Remark nearest: partial-fraction bound E(n) on the error, n >= 1
            res = [(z, -Np(z) / (z * dDp(z))) for z in roots if abs(z - t0) > mp.mpf(10) ** -20]
            E = lambda n: sum(abs(c) * abs(z) ** (-n) for z, c in res)
            n0 = max([n for n in range(1, 81) if E(n) >= 0.5], default=0) + 1
            print(f"  q = {lab}: E(n) < 1/2 for {n0} <= n <= 80")
            check(f"q = {lab}: rounding bound E(n) < 1/2 from n = {ROUND_N0[q]} on",
                  n0 == ROUND_N0[q], f"({n0})")
        table[lab] = (psi, C1)
    printed = {  # Table 3 of the paper: psi_q, C_q, 1/(1 + psi_q)
        3: ("1.4655712319", "0.7019310679", "0.4055855240"),
        4: ("1.5701473122", "0.7569789423", "0.3890827562"),
        5: ("1.6013473338", "0.7487899136", "0.3844161781"),
        6: ("1.6119303966", "0.7378594370", "0.3828585943"),
        'inf': ("1.6180339887", "0.7236067977", "0.3819660113")}
    for lab, (ps, cs, bs) in printed.items():
        psi, C = table[lab]
        def ten(z):                                                   # rounded to ten decimals
            k = int(mp.nint(z * 10 ** 10))
            return f"{k // 10 ** 10}.{k % 10 ** 10:010d}"
        got = (ten(psi), ten(C), ten(1 / (1 + psi)))
        check(f"Table 3 row q = {lab} matches", got == (ps, cs, bs), f"{got}")
    check("psi_3 < psi_4 < psi_5 < psi_6 < phi",
          table[3][0] < table[4][0] < table[5][0] < table[6][0] < table['inf'][0])
    check("C_inf = phi/sqrt 5", abs(table['inf'][1] - mp.phi / mp.sqrt(5)) < mp.mpf(10) ** -30)
    # blue share at the largest BFS rank, as a sanity check of 1/(1 + psi)
    for key, q in ((2, 4), (3, 6)):
        rank, how, counts, rpos = results[key]
        n = len(counts) - 1
        share = mp.mpf(rpos[n - 1]) / counts[n]
        print(f"  m = {key}: share of negatives at rank {n} is {mp.nstr(share, 8)}, "
              f"1/(1 + psi) = {mp.nstr(1 / (1 + table[q][0]), 8)}")

    print(f"\ntotal {time.time() - T0:.0f}s;", "ALL CHECKS PASSED" if not FAIL else f"FAILED: {FAIL}")
    sys.exit(1 if FAIL else 0)


if __name__ == '__main__':
    main()
