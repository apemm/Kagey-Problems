"""Exact checks of the complete graph, Section `sec:complete` of Paper C1, for small N.

Q = J - dI, so the chain keeps its state with probability p = 1 - (d-1)h and moves to each other
state with probability h. All laws are computed in exact rational arithmetic by a dynamic program
over (composition, last state), which does not use the run expansion.

  A. Theorem `thm:simplex-balance` (exact balancing). For d = 2, 3, 4, every N from 2 to 9 (to 7
     for d = 4) and
     p in {1/d, 1/d + 1/50, ..., 49/50}, with the uniform start, the most likely compositions with a
     given support are exactly the balanced ones, and each move of one unit from a coordinate b to
     a coordinate a with n_b >= n_a + 2 and n_a >= 1 strictly increases the probability.
  B. The uniform start is needed. For d = 2, N = 4 and the start in state 1, the face {1,2} has
     the unique maximizer (3,1) at T = 1/2, 1 and 3/2, with the probabilities quoted in the
     introduction of the paper.
  C. Theorem `thm:simplex-crossing`(i). For d = 3, k = 2, 3 and N = k, ..., 12, the polynomial
     S_n(u) = P_N(n)/V_N of a balanced composition n has nonnegative coefficients, lowest term
     k! u^(k-1), and next coefficient k!(k-1)(N-k)/2. Its root in u decreases strictly in N, and
     p_{k,k} = 1/(1 + (d-1)(k!)^(-1/(k-1))). The root is found by bisection on the exact polynomial.
  D. Remark `rem:simplex-edge-mode`: d = 3, N = 4, p = 10/17 gives P_4(2,2,0)/V_4 = 4123/4000 and
     P_4(2,1,1)/V_4 = 3969/4000, and the three edge centers are the only global modes.

Every check is an assertion. Nothing in the paper is deduced from these numbers.
Needs only the Python standard library. Run:  py -I verify_complete.py   (under a minute)
"""
from fractions import Fraction
from itertools import product
from math import factorial

CHECKS = 0


def ok(cond, what):
    global CHECKS
    if not cond:
        raise AssertionError(what)
    CHECKS += 1
    print("  ok   ", what, flush=True)


def law(d, N, p, mu):
    """Exact law of the composition for Q = J - dI at keep probability p, start mu."""
    h = (1 - p) / (d - 1)
    cur = {}
    for a in range(d):
        if mu[a]:
            n = [0] * d
            n[a] = 1
            cur[(tuple(n), a)] = mu[a]
    for _ in range(N - 1):
        nxt = {}
        for (n, a), w in cur.items():
            for b in range(d):
                m = list(n)
                m[b] += 1
                key = (tuple(m), b)
                nxt[key] = nxt.get(key, 0) + w * (p if a == b else h)
        cur = nxt
    out = {}
    for (n, _), w in cur.items():
        out[n] = out.get(n, 0) + w
    return out


def balanced(n):
    pos = [x for x in n if x > 0]
    return max(pos) - min(pos) <= 1


def support(n):
    return tuple(i for i, x in enumerate(n) if x > 0)


def part_a():
    print("A. Exact balancing with the uniform start (Theorem thm:simplex-balance)")
    for d in (2, 3, 4):
        Nmax = 9 if d < 4 else 7
        grid = [Fraction(1, d)] + [Fraction(j, 50) for j in range(1, 50) if Fraction(j, 50) > Fraction(1, d)]
        cases = 0
        for N in range(2, Nmax + 1):
            for p in grid:
                P = law(d, N, p, [Fraction(1, d)] * d)
                faces = {}
                for n, w in P.items():
                    faces.setdefault(support(n), []).append((w, n))
                for F, lst in faces.items():
                    best = max(w for w, _ in lst)
                    argmax = {n for w, n in lst if w == best}
                    bal = {n for _, n in lst if balanced(n)}
                    assert argmax == bal, (d, N, p, F, argmax, bal)
                    for w, n in lst:
                        for a, b in product(F, F):
                            if n[b] >= n[a] + 2:
                                m = list(n)
                                m[a] += 1
                                m[b] -= 1
                                assert P[tuple(m)] > w, (d, N, p, n, a, b)
                    cases += 1
        ok(True, f"d = {d}, N = 2..{Nmax}, {len(grid)} values of p in [1/d, 1): balanced maximizers and strict moves on {cases} faces")


def part_b():
    print("B. A start in state 1 breaks balancing (d = 2, N = 4)")
    want = {Fraction(1, 2): (Fraction(63, 512), Fraction(57, 512), Fraction(49, 512)),
            Fraction(1): (Fraction(15, 64), Fraction(13, 64), Fraction(9, 64)),
            Fraction(3, 2): (Fraction(165, 512), Fraction(147, 512), Fraction(75, 512))}
    for T, vals in want.items():
        p = 1 - T / 4
        P = law(2, 4, p, [1, 0])
        got = (P[(3, 1)], P[(2, 2)], P[(1, 3)])
        ok(got == vals and got[0] > got[1] > got[2],
           f"T = {T}: P(3,1), P(2,2), P(1,3) = {', '.join(str(g) for g in got)}, so (3,1) is the unique maximizer")


def S_poly(n):
    """Coefficients of S_n(u): the number of words with counts n and j switches, by j."""
    d = len(n)
    cur = {}
    for a in range(d):
        if n[a]:
            m = [0] * d
            m[a] = 1
            cur[(tuple(m), a, 0)] = 1
    for _ in range(sum(n) - 1):
        nxt = {}
        for (m, a, j), c in cur.items():
            for b in range(d):
                if m[b] < n[b]:
                    mm = list(m)
                    mm[b] += 1
                    key = (tuple(mm), b, j + (a != b))
                    nxt[key] = nxt.get(key, 0) + c
        cur = nxt
    coef = {}
    for (_, _, j), c in cur.items():
        coef[j] = coef.get(j, 0) + c
    return [coef.get(j, 0) for j in range(max(coef) + 1)]


def root(coef):
    lo, hi = Fraction(0), Fraction(1)
    val = lambda u: sum(c * u ** j for j, c in enumerate(coef)) - 1
    while val(hi) < 0:
        hi *= 2
    for _ in range(60):
        mid = (lo + hi) / 2
        if val(mid) < 0:
            lo = mid
        else:
            hi = mid
    return float((lo + hi) / 2)


def part_c():
    print("C. One crossing with a vertex (Theorem thm:simplex-crossing(i)), d = 3")
    d = 3
    for k in (2, 3):
        roots = []
        for N in range(k, 13):
            n = [N // k + (1 if i < N % k else 0) for i in range(k)]
            coef = S_poly(n)
            low = min(j for j, c in enumerate(coef) if c)
            ok(all(c >= 0 for c in coef) and low == k - 1 and coef[k - 1] == factorial(k)
               and (N == k or coef[k] == factorial(k) * (k - 1) * (N - k) // 2),
               f"k = {k}, n = {tuple(n)}: coefficients >= 0, lowest k! u^(k-1) = {coef[k - 1]} u^{k - 1}, "
               f"next {coef[k] if len(coef) > k else 0}")
            roots.append(root(coef))
        ok(all(a > b for a, b in zip(roots, roots[1:])), f"k = {k}: the root u_N decreases strictly for N = {k}..12")
        pkk = 1 / (1 + (d - 1) * roots[0])
        ok(abs(pkk - 1 / (1 + (d - 1) * factorial(k) ** (-1 / (k - 1)))) < 1e-12 and roots[0] < 1,
           f"k = {k}: p_(k,k) = {pkk:.12f} = 1/(1 + (d-1)(k!)^(-1/(k-1))), and u <= (k!)^(-1/(k-1)) < 1")


def part_d():
    print("D. An intermediate face is a mode at N = 4 (Remark rem:simplex-edge-mode)")
    d, N, p = 3, 4, Fraction(10, 17)
    P = law(d, N, p, [Fraction(1, 3)] * 3)
    V = P[(4, 0, 0)]
    ok(P[(2, 2, 0)] / V == Fraction(4123, 4000) and P[(2, 1, 1)] / V == Fraction(3969, 4000),
       "P_4(2,2,0)/V_4 = 4123/4000 and P_4(2,1,1)/V_4 = 3969/4000")
    top = max(P.values())
    modes = sorted(n for n, w in P.items() if w == top)
    ok(modes == [(0, 2, 2), (2, 0, 2), (2, 2, 0)], f"the global modes are exactly {modes}")


def main():
    part_a()
    part_b()
    part_c()
    part_d()
    print(f"verify_complete: all {CHECKS} checks passed")


if __name__ == "__main__":
    main()
