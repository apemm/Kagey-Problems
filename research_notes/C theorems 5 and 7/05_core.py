"""Exact Arrhenius machinery for route T7-B (depth, prefactor, cycles, suppression).

Laurent polynomials in t = exp(-1/eta) are dicts {exponent: integer coefficient}.
The cost matrix V has integer entries V[i][j] >= 0 (i != j), q_ij = t^V[i][j].
Killed matrices keep the full exit diagonal (see 01_cycle_conjecture_math.md, 2A).
Run through the drivers 05_run_*.py with  py -I.
"""

from fractions import Fraction
from itertools import combinations
import sympy as sp


# ---------- Laurent polynomial arithmetic ----------
def padd(a, b):
    z = dict(a)
    for k, v in b.items():
        z[k] = z.get(k, 0) + v
    return {k: v for k, v in z.items() if v}


def pneg(a):
    return {k: -v for k, v in a.items()}


def pmul(a, b):
    z = {}
    for i, u in a.items():
        for j, v in b.items():
            z[i + j] = z.get(i + j, 0) + u * v
    return {k: v for k, v in z.items() if v}


def nu(p):
    """First nonzero exponent (None for the zero polynomial)."""
    return min(p) if p else None


class PM:
    """Matrix of Laurent polynomials with cached minors (Laplace along the first row)."""

    def __init__(self, a):
        self.a = a
        self.n = len(a)
        self.cache = {}

    def det(self, rows, cols):
        if not rows:
            return {0: 1}
        key = (rows, cols)
        if key in self.cache:
            return self.cache[key]
        r, rest = rows[0], rows[1:]
        tot = {}
        for idx, c in enumerate(cols):
            e = self.a[r][c]
            if not e:
                continue
            sub = self.det(rest, cols[:idx] + cols[idx + 1:])
            if not sub:
                continue
            term = pmul(e, sub)
            if idx % 2:
                term = pneg(term)
            tot = padd(tot, term)
        self.cache[key] = tot
        return tot

    def pdet(self, S):
        S = tuple(S)
        return self.det(S, S)


def build_A(V, extra=None):
    """A = -Q with the full exit diagonal; extra[i] is an added killing polynomial."""
    n = len(V)
    a = [[{} for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if i != j:
                a[i][j] = {V[i][j]: -1}
                a[i][i] = padd(a[i][i], {V[i][j]: 1})
        if extra and extra[i]:
            a[i][i] = padd(a[i][i], extra[i])
    return a


def proper_faces(n):
    return [f for k in range(1, n) for f in combinations(range(n), k)]


def all_faces(n):
    return [f for k in range(1, n + 1) for f in combinations(range(n), k)]


# ---------- depth (24) and prefactor (23) ----------
def depth(pm, S):
    d = nu(pm.pdet(S))
    assert d is not None, "singular killed matrix"
    subs = [nu(pm.pdet(tuple(x for x in S if x != i))) for i in S]
    return d - min(subs)


def limit_matrix(pm, S):
    """B = lim t^D A_S^{-1}, as a Fraction matrix, and D."""
    S = tuple(S)
    k = len(S)
    den = pm.pdet(S)
    w = nu(den)
    D = depth(pm, S)
    B = [[Fraction(0)] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            rows = tuple(x for x in S if x != S[j])
            cols = tuple(x for x in S if x != S[i])
            num = pm.det(rows, cols)
            if (i + j) % 2:
                num = pneg(num)
            if not num:
                continue
            e = nu(num) - w + D
            assert e >= 0, "inverse entry exceeds the claimed depth"
            if e == 0:
                B[i][j] = Fraction(num[nu(num)], den[w])
    return B, D


def spectral_radius(B):
    lam = sp.Symbol("lam")
    M = sp.Matrix([[sp.Rational(x.numerator, x.denominator) for x in r] for r in B])
    p = sp.Poly(M.charpoly(lam).as_expr(), lam)
    roots = p.real_roots()
    rho = max(roots, key=lambda r: sp.N(r, 50))
    assert sp.N(rho, 30) > 0
    return rho


def prefactor(pm, S):
    B, D = limit_matrix(pm, S)
    rho = spectral_radius(B)
    return D, 1 / rho


def show(x):
    """Exact string for a sympy number (rational when it is rational)."""
    if x.is_Rational:
        return str(x)
    return "%s ~ %s" % (sp.srepr(x)[:0] + "alg", sp.N(x, 12))


# ---------- global cycles from exit probabilities (definition) ----------
def exit_exponent(V, base_pm, C, x, y):
    """nu(P_x(exit C before hitting y)) via Cramer on the row-scaled jump-chain system."""
    L = tuple(z for z in C if z != y)
    den = base_pm.pdet(L)
    pos = L.index(x)
    mat = [[base_pm.a[i][j] for j in L] for i in L]
    for r, z in enumerate(L):
        rz = {}
        for w in range(len(V)):
            if w not in C:
                rz = padd(rz, {V[z][w]: 1})
        mat[r][pos] = rz
    num = PM(mat).pdet(tuple(range(len(L))))
    return nu(num) - nu(den)


def is_cycle(V, base_pm, C):
    if len(C) == 1:
        return True
    return all(exit_exponent(V, base_pm, C, x, y) > 0
               for x in C for y in C if x != y)


def jump_chain_exit_exponent(V, C, x, y):
    """Same quantity with the embedded jump chain in sympy rational functions (cross-check)."""
    t = sp.Symbol("t")
    n = len(V)
    q = [[None if i == j else t ** V[i][j] for j in range(n)] for i in range(n)]
    qi = [sum(q[i][j] for j in range(n) if j != i) for i in range(n)]
    L = [z for z in C if z != y]
    A = sp.zeros(len(L), len(L))
    b = sp.zeros(len(L), 1)
    for r, z in enumerate(L):
        for c, w in enumerate(L):
            A[r, c] = (1 if r == c else 0) - (q[z][w] / qi[z] if z != w else 0)
        b[r] = sum(q[z][w] / qi[z] for w in range(n) if w not in C)
    u = A.LUsolve(b)[L.index(x)]
    num, den = sp.fraction(sp.cancel(sp.together(u)))
    lo = lambda e: min(m[0] for m in sp.Poly(e, t).monoms())
    return lo(num) - lo(den)


# ---------- the whole analysis of one cost matrix ----------
def analyze(V, rev=None):
    """rev = (U, H) for reversible data, else None."""
    n = len(V)
    base = PM(build_A(V))
    faces = proper_faces(n)
    D = {f: depth(base, f) for f in faces}
    cyc = {f: is_cycle(V, base, f) for f in faces}
    crit = {}
    for f in faces:
        crit[f] = all(D[f] > D[g] for k in range(1, len(f)) for g in combinations(f, k))
    # Theorem D consistency: D(F) = max D(C) over cycles C subset F
    thmD = all(D[f] == max(D[c] for c in faces if cyc[c] and set(c) <= set(f)) for f in faces)
    singles = all(D[(i,)] == min(V[i][j] for j in range(n) if j != i) for i in range(n))
    out = {"D": D, "cycle": cyc, "criterion": crit, "thmD": thmD, "singleton_formula": singles}
    if rev is not None:
        U, H = rev
        ok = True
        for f in faces:
            if len(f) == 1:
                continue
            b = min(H[i][j] for i in f for j in range(n) if j not in f)
            par = list(range(n))

            def find(a):
                while par[a] != a:
                    par[a] = par[par[a]]
                    a = par[a]
                return a
            for i in range(n):
                for j in range(i + 1, n):
                    if H[i][j] < b:
                        par[find(i)] = find(j)
            energy = len({find(i) for i in f}) == 1
            if energy != cyc[f]:
                ok = False
            if cyc[f] and D[f] != b - min(U[i] for i in f):
                ok = False
        out["energy_cycle_agrees"] = ok
    out["disagreements"] = []
    for f in faces:
        if cyc[f] != crit[f]:
            sub = [D[g] for k in range(1, len(f)) for g in combinations(f, k)]
            kind = ("tie (cycle, D(C) = max D(C'))" if cyc[f] and D[f] == max(sub)
                    else "genuine failure")
            out["disagreements"].append({"C": [i + 1 for i in f], "truth_cycle": cyc[f],
                                         "criterion": crit[f], "D": D[f], "class": kind})
    return out, base


# ---------- suppression observable: exact finite-eta scores ----------
def _charpoly(A):
    """Faddeev-LeVerrier over Fractions: [1, c1, ..., cn] with det(lam I - A) = sum c_k lam^(n-k)."""
    n = len(A)
    Mk = [[Fraction(0)] * n for _ in range(n)]
    ck = Fraction(1)
    out = [ck]
    for k in range(1, n + 1):
        AM = [[sum(A[i][l] * Mk[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        Mk = [[AM[i][j] + (ck if i == j else 0) for j in range(n)] for i in range(n)]
        AMk = [[sum(A[i][l] * Mk[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        ck = -sum(AMk[i][i] for i in range(n)) / k
        out.append(ck)
    return out


def smallest_eig(A, dps, tol_digits):
    """Smallest real eigenvalue of an irreducible nonsingular M-matrix with Fraction entries.

    Newton's method on det(lam I - A) started at 0.  With eigenvalues l_i (smallest l_1, real,
    simple) the Newton step is 1/sum_i Re 1/(l_i - lam) <= l_1 - lam, so the iteration increases
    monotonically to l_1 and never overshoots; the characteristic polynomial is exact (Fractions)
    and evaluated at dps digits.
    """
    import mpmath as mp
    mp.mp.dps = dps
    c = [mp.mpf(x.numerator) / mp.mpf(x.denominator) for x in _charpoly(A)]
    n = len(A)
    lam = mp.mpf(0)
    tol = mp.mpf(10) ** (-tol_digits)
    for _ in range(20000):
        p = c[0]
        dp = mp.mpf(0)
        for k in range(1, n + 1):
            dp = dp * lam + p
            p = p * lam + c[k]
        new = lam - p / dp
        if abs(new - lam) <= tol * abs(new):
            return new
        lam = new
    raise RuntimeError("Newton did not converge")


def numeric_winners(V, F, g, texp, hmax=60):
    """Winners of Phi_G(h) = (|G|-1) + t^(-h) lambda_G(v), G over all nonempty subsets of E.

    Field v_k = -M for k outside F: killing M = t^(-g) is added to A_G on G minus F
    (g > 0 strong, g = 0 means M = 1, g < 0 weak).  The matrix entries are the exact rationals
    t^V_ij at t = 10^(-texp); lambda_G(v) is the smallest real eigenvalue, obtained from exact
    real-root isolation of the exact characteristic polynomial and evaluated to a precision far
    above the exponent gaps.  Only the final scores are floating (mpmath).  The driver runs two
    values of t and requires the winner sequences to agree.
    Heights are sampled at h = j/4 + 1/8 until the winner is not contained in F.
    Returns (winners as 0-based tuples, heights).
    """
    import mpmath as mp
    n = len(V)
    dps = 100 + texp * (3 * abs(g) + 40)
    tol_digits = texp * (abs(g) + 25)
    mp.mp.dps = dps
    t = Fraction(1, 10 ** texp)
    lam = {}
    for G in all_faces(n):
        A = [[Fraction(0)] * len(G) for _ in G]
        for a, i in enumerate(G):
            for b, j in enumerate(G):
                if i != j:
                    A[a][b] = -(t ** V[i][j])
            A[a][a] = (sum(t ** V[i][j] for j in range(n) if j != i)
                       + (t ** (-g) if i not in F else 0))
        lam[G] = smallest_eig(A, dps, tol_digits)
    tm = mp.mpf(10) ** (-texp)
    winners, heights = [], []
    for j in range(4 * hmax):
        h = Fraction(j, 4) + Fraction(1, 8)
        tau = tm ** (-(mp.mpf(h.numerator) / h.denominator))
        sc = {G: (len(G) - 1) + tau * lam[G] for G in lam}
        w = min(sc, key=lambda G: sc[G])
        winners.append(w)
        heights.append(h)
        if not set(w) <= set(F):
            break
    return winners, heights
