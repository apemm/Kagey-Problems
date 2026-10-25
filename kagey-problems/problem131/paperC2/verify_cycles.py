"""Exact checks of the two Arrhenius examples of Section `sec:lowtemp`.

Example `ex:four-state` (a noncycle winner on an open window) and Example `ex:branch-switch`
(a branch switch). The rates are q_ij = t^(H_ij - U_i) with t = exp(-1/eta), so every killed
matrix -Q_F (with the full exit rates on its diagonal) is a matrix of polynomials in t with
integer coefficients. We compute in exact integer and rational arithmetic:

  * the determinant of -Q_F and its adjugate for every proper face F, as polynomials in t;
  * the depth D(F) = (order of det(-Q_F)) - (least order of a diagonal cofactor), which is the
    exponent of the leading term of the largest entry of (-Q_F)^(-1), and the check that it equals
    the largest depth of a cycle contained in F (Theorem `thm:depth`), with the cycles found by
    the energy criterion of the example;
  * for the faces of depth 3 the limit B_F = lim t^3 (-Q_F)^(-1), its spectral radius and the
    prefactor a_F = 1/rho(B_F) of Proposition `prop:prefactor`;
  * the exact polynomials det(-Q_12) and det(-Q_123) = det(-Q_124) quoted in the Lean map, the
    limiting scores 1 + 2x, 2 + 2x/3, 2 + 2x and 3, and the three windows (0, 3/4), (3/4, 3/2),
    (3/2, oo) with the score 8/3 at x = 1;
  * for the branch switch the depths 3, 1, 1 of the singletons and 5 of the cycle {2,3}.

Standard library only. Run:  py -I verify_cycles.py   (under a second)
"""

from fractions import Fraction
from itertools import combinations, permutations

CHECKS = 0


def ok(cond, what):
    global CHECKS
    if not cond:
        raise AssertionError(what)
    CHECKS += 1
    print("  ok   ", what)


def add(a, b):
    z = dict(a)
    for k, v in b.items():
        z[k] = z.get(k, 0) + v
    return {k: v for k, v in z.items() if v}


def neg(a):
    return {k: -v for k, v in a.items()}


def mul(a, b):
    z = {}
    for i, u in a.items():
        for j, v in b.items():
            z[i + j] = z.get(i + j, 0) + u * v
    return {k: v for k, v in z.items() if v}


def det(a):
    n = len(a)
    total = {}
    for p in permutations(range(n)):
        parity = sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n))
        term = {0: (-1) ** parity}
        for i in range(n):
            term = mul(term, a[i][p[i]])
        total = add(total, term)
    return total


def minor(a, row, col):
    return [[v for j, v in enumerate(r) if j != col]
            for i, r in enumerate(a) if i != row]


def killed(u, h):
    """-Q with the full exit diagonal, as polynomials {exponent: coefficient} in t."""
    n = len(u)
    v = [[None if i == j else h[i][j] - u[i] for j in range(n)] for i in range(n)]
    assert all(v[i][j] >= 0 and u[i] + v[i][j] == u[j] + v[j][i]
               for i in range(n) for j in range(n) if i != j)
    a = [[{} for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i != j:
                a[i][j] = {v[i][j]: -1}
                a[i][i] = add(a[i][i], {v[i][j]: 1})
    return a, v


def spectral_radius(b):
    """Spectral radius of the rational limit matrices that occur here: one nonzero column, or
    rank one with equal row sums (both cases are asserted)."""
    k = len(b)
    nonzero_cols = [j for j in range(k) if any(b[i][j] for i in range(k))]
    if len(nonzero_cols) == 1:
        j = nonzero_cols[0]
        return b[j][j]
    sums = [sum(r) for r in b]
    assert all(s == sums[0] for s in sums)
    return sums[0]


def analyze(u, h, critical_depth):
    n = len(u)
    a, v = killed(u, h)
    result = []
    for k in range(1, n):
        for f in combinations(range(n), k):
            af = [[a[i][j] for j in f] for i in f]
            denominator = det(af)
            w = min(denominator)
            adj = [[det(minor(af, j, i)) for j in range(k)] for i in range(k)]
            for i in range(k):
                for j in range(k):
                    if (i + j) % 2:
                        adj[i][j] = neg(adj[i][j])
            d = w - min(min(adj[i][i]) for i in range(k))
            b = [[Fraction(0) for _ in f] for _ in f]
            for i in range(k):
                for j in range(k):
                    num = adj[i][j]
                    assert num and min(num) + d >= w
                    if min(num) + d == w:
                        b[i][j] = Fraction(num[min(num)], denominator[w])
            boundary = min(h[i][j] for i in f for j in range(n) if j not in f)
            reached = {f[0]}
            while True:
                more = {j for i in reached for j in f if i != j and h[i][j] < boundary}
                if more <= reached:
                    break
                reached |= more
            cycle = k == 1 or reached == set(f)
            row = {"F": tuple(i + 1 for i in f), "D": d, "cycle": cycle, "det": denominator,
                   "adj": adj}
            if cycle:
                row["cycle_depth"] = boundary - min(u[i] for i in f)
            if d == critical_depth:
                row["B"] = b
                row["a"] = 1 / spectral_radius(b)
            result.append(row)
    return result


def main():
    print("Example ex:four-state: U = (0,1,1,1), H12 = 2, H13 = H23 = H34 = 3, H14 = H24 = 5")
    U = [0, 1, 1, 1]
    H = [[0, 2, 3, 5], [2, 0, 3, 5], [3, 3, 0, 3], [5, 5, 3, 0]]
    a, V = killed(U, H)
    ok(V == [[None, 2, 3, 5], [1, None, 2, 4], [2, 2, None, 2], [4, 4, 2, None]],
       "the rates are t^V with V = (2,3,5; 1,2,4; 2,2,2; 4,4,2) as displayed")
    ok([a[i][i] for i in range(4)] == [{2: 1, 3: 1, 5: 1}, {1: 1, 2: 1, 4: 1}, {2: 3}, {2: 1, 4: 2}],
       "exit rates q1 = t^2+t^3+t^5, q2 = t+t^2+t^4, q3 = 3t^2, q4 = t^2+2t^4")
    rows = analyze(U, H, 3)
    for r in rows:
        if r["cycle"]:
            assert r["cycle_depth"] == r["D"], r
    ok(all(r["D"] == max(c["D"] for c in rows if c["cycle"] and set(c["F"]) <= set(r["F"]))
           for r in rows),
       "D(F) is the largest depth of a cycle in F, for all 14 proper faces (Theorem thm:depth)")
    cyc = [r["F"] for r in rows if r["cycle"] and len(r["F"]) > 1]
    ok(cyc == [(1, 2)], "the only proper cycle with more than one state is {1,2}, of depth 3")
    ok([r["D"] for r in rows if len(r["F"]) == 1] == [2, 1, 2, 2], "singleton depths 2, 1, 2, 2")
    deep = {r["F"]: r for r in rows if r["D"] == 3}
    ok(sorted(deep) == [(1, 2), (1, 2, 3), (1, 2, 4)],
       "the faces of depth 3 are {1,2}, {1,2,3}, {1,2,4}; every other proper face has depth <= 2")
    ok(deep[(1, 2)]["det"] == {4: 2, 5: 1, 6: 2, 7: 2, 9: 1},
       "det(-Q_12) = 2t^4 + t^5 + 2t^6 + 2t^7 + t^9")
    ok(deep[(1, 2, 3)]["det"] == deep[(1, 2, 4)]["det"] == {6: 2, 7: 1, 8: 6, 9: 4, 11: 3},
       "det(-Q_123) = det(-Q_124) = 2t^6 + t^7 + 6t^8 + 4t^9 + 3t^11")
    lead = lambda p: (min(p), p[min(p)])
    adj123 = deep[(1, 2, 3)]["adj"]
    ok([lead(adj123[i][0]) for i in range(3)] == [(3, 3), (3, 3), (3, 2)]
       and all(min(adj123[i][j]) >= 4 for i in range(3) for j in (1, 2) if adj123[i][j]),
       "adjugate of -Q_123: first column (3t^3, 3t^3, 2t^3) + O(t^4), other entries O(t^4)")
    adj124 = deep[(1, 2, 4)]["adj"]
    ok([lead(adj124[i][0]) for i in range(2)] == [(3, 1), (3, 1)] and min(adj124[2][0]) >= 4
       and all(min(adj124[i][j]) >= 4 for i in range(3) for j in (1, 2) if adj124[i][j]),
       "adjugate of -Q_124: first column (t^3, t^3, 0) + O(t^4), other entries O(t^4)")
    adj12 = deep[(1, 2)]["adj"]
    ok([lead(adj12[i][0]) for i in range(2)] == [(1, 1), (1, 1)]
       and all(min(adj12[i][1]) >= 2 for i in range(2)),
       "adjugate of -Q_12: first column (t, t) + O(t^2), second column O(t^2)")
    half, one = Fraction(1, 2), Fraction(1)
    ok([[x for x in r] for r in deep[(1, 2)]["B"]] == [[half, 0], [half, 0]]
       and [r[0] for r in deep[(1, 2, 3)]["B"]] == [Fraction(3, 2), Fraction(3, 2), one]
       and [r[0] for r in deep[(1, 2, 4)]["B"]] == [half, half, 0],
       "B_12, B_123, B_124 have first columns (1/2,1/2), (3/2,3/2,1), (1/2,1/2,0), zeros elsewhere")
    pref = {F: deep[F]["a"] for F in deep}
    ok(pref == {(1, 2): 2, (1, 2, 3): Fraction(2, 3), (1, 2, 4): 2},
       "prefactors a_12 = 2, a_123 = 2/3, a_124 = 2 (Proposition prop:prefactor)")
    score = {(1, 2): lambda x: 1 + 2 * x, (1, 2, 3): lambda x: 2 + Fraction(2, 3) * x,
             (1, 2, 4): lambda x: 2 + 2 * x, (1, 2, 3, 4): lambda x: Fraction(3)}
    for F in deep:
        assert score[F](Fraction(1)) == len(F) - 1 + pref[F]
    grid = [Fraction(j, 64) for j in range(1, 256)]
    win = {}
    for x in grid:
        vals = {F: s(x) for F, s in score.items()}
        m = min(vals.values())
        best = [F for F in vals if vals[F] == m]
        if len(best) == 1:
            win[x] = best[0]
        else:
            ok(x in (Fraction(3, 4), Fraction(3, 2)), f"tie at x = {x}, one of the two window ends")
    ok(all(win[x] == (1, 2) for x in win if x < Fraction(3, 4))
       and all(win[x] == (1, 2, 3) for x in win if Fraction(3, 4) < x < Fraction(3, 2))
       and all(win[x] == (1, 2, 3, 4) for x in win if x > Fraction(3, 2)),
       "unique minimizer {1,2} on (0,3/4), {1,2,3} on (3/4,3/2), V on (3/2,4) (grid of step 1/64)")
    ok(all(score[(1, 2, 4)](x) - score[(1, 2)](x) == 1 for x in grid), "{1,2,4} is always 1 above {1,2}")
    ok(score[(1, 2, 3)](Fraction(1)) == Fraction(8, 3) and score[(1, 2)](Fraction(1)) == 3,
       "at x = 1 the noncycle {1,2,3} scores 8/3 < 3 = score of {1,2} and of V")

    print("Example ex:branch-switch: U = (2,0,0), H12 = H13 = 5, H23 = 1")
    U = [2, 0, 0]
    H = [[0, 5, 5], [5, 0, 1], [5, 1, 0]]
    a, V = killed(U, H)
    ok(V == [[None, 3, 3], [5, None, 1], [5, 1, None]],
       "q12 = q13 = t^3, q21 = q31 = t^5, q23 = q32 = t")
    rows = analyze(U, H, 5)
    D = {r["F"]: r["D"] for r in rows}
    ok(D[(1,)] == 3 and D[(2,)] == 1 and D[(3,)] == 1, "singleton depths 3, 1, 1")
    ok(D[(2, 3)] == 5 and [r["F"] for r in rows if r["cycle"] and len(r["F"]) > 1] == [(2, 3)],
       "{2,3} is the only proper cycle with two states, of depth 5; {1,2}, {1,3} are not cycles")
    ok(all(r["D"] == max(c["D"] for c in rows if c["cycle"] and set(c["F"]) <= set(r["F"]))
           for r in rows), "D(F) is the largest depth of a cycle in F, for all 6 proper faces")
    print(f"verify_cycles: all {CHECKS} checks passed")


if __name__ == "__main__":
    main()
