# Verification for Kagey Problem 131 (Galton board with persistence p)
#
# N = number of bounces, bins k = 0..N (k = number of right bounces); Kagey's row n is N = n - 1.
# Method A: closed form (run counts).  Method B: two-state dynamic program.
# Method C: enumeration of all 2^N words.  Exact arithmetic (Fraction / int) unless marked "float".
import sys, time, cmath
from fractions import Fraction as F
from itertools import product
from math import comb, log, sqrt, erf, factorial

t0 = time.time()
results = []

def report(name, ok, extra=""):
    results.append(ok)
    print("%-72s %s %s" % (name, "PASS" if ok else "FAIL", extra), flush=True)

NBRUTE = 16
NDP = 40
GRID = [F(i, 16) for i in range(17)] + [F(1, 3), F(2, 3), F(5, 6)]

# ---------------------------------------------------------------- method A
def W(N, k, j):
    """number of words with k R's, N-k L's and exactly j direction changes"""
    a, b = k, N - k
    if a == 0 or b == 0:
        return (1 if j == 0 else 0) if N >= 1 else 0
    if j == 0:
        return 0
    if j % 2 == 1:
        i = (j + 1) // 2
        return 2 * comb(a - 1, i - 1) * comb(b - 1, i - 1)
    i = j // 2
    return comb(a - 1, i) * comb(b - 1, i - 1) + comb(a - 1, i - 1) * comb(b - 1, i)

def pmf_A(N, p):
    if N == 0:
        return [F(1)]
    q = 1 - p
    return [sum(W(N, k, j) * p**(N - 1 - j) * q**j for j in range(N)) / 2 for k in range(N + 1)]

# ---------------------------------------------------------------- method B
def pmf_B(N, p):
    if N == 0:
        return [F(1)]
    q = 1 - p
    R = [F(0), F(1, 2)]
    L = [F(1, 2), F(0)]
    for n in range(2, N + 1):
        R2 = [F(0)] * (n + 1)
        L2 = [F(0)] * (n + 1)
        for k in range(n + 1):
            if k >= 1:
                R2[k] = p * R[k - 1] + q * L[k - 1]
            if k <= n - 1:
                L2[k] = p * L[k] + q * R[k]
        R, L = R2, L2
    return [R[k] + L[k] for k in range(N + 1)]

# ---------------------------------------------------------------- method C
brute_W = {}
for N in range(1, NBRUTE + 1):
    tab = {}
    for w in product((0, 1), repeat=N):
        k = sum(w)
        j = sum(1 for i in range(N - 1) if w[i] != w[i + 1])
        tab[(k, j)] = tab.get((k, j), 0) + 1
    brute_W[N] = tab

def pmf_C(N, p):
    if N == 0:
        return [F(1)]
    q = 1 - p
    out = [F(0)] * (N + 1)
    for (k, j), c in brute_W[N].items():
        out[k] += F(c, 2) * p**(N - 1 - j) * q**j
    return out

# ---- check 1: run-count formula against enumeration
ok = all(brute_W[N].get((k, j), 0) == W(N, k, j)
         for N in range(1, NBRUTE + 1) for k in range(N + 1) for j in range(N))
report("1. run counts W(N,k,j) = enumeration, N<=%d" % NBRUTE, ok)

# ---- check 2: three methods agree; rows sum to 1
ok = True
for p in GRID:
    for N in range(0, NBRUTE + 1):
        a, b, c = pmf_A(N, p), pmf_B(N, p), pmf_C(N, p)
        if not (a == b == c and sum(a) == 1):
            ok = False
report("2. pmf: closed form = DP = enumeration, rows sum to 1, N<=%d, %d values of p" % (NBRUTE, len(GRID)), ok)
ok = True
for p in GRID:
    for N in range(NBRUTE + 1, NDP + 1, 3):
        a, b = pmf_A(N, p), pmf_B(N, p)
        if not (a == b and sum(a) == 1):
            ok = False
report("3. pmf: closed form = DP, rows sum to 1, N<=%d" % NDP, ok)

# ---- check 4: Kagey's three numerator tables (rows 1..9 of his figure)
FIG = {
    (1, 2): [[1], [1, 1], [1, 4, 1], [1, 8, 8, 1], [1, 12, 28, 12, 1], [1, 16, 64, 64, 16, 1],
             [1, 20, 116, 212, 116, 20, 1], [1, 24, 184, 520, 520, 184, 24, 1],
             [1, 28, 268, 1052, 1676, 1052, 268, 28, 1]],
    (2, 1): [[1], [1, 1], [2, 2, 2], [4, 5, 5, 4], [8, 12, 14, 12, 8], [16, 28, 37, 37, 28, 16],
             [32, 64, 94, 106, 94, 64, 32], [64, 144, 232, 289, 289, 232, 144, 64],
             [128, 320, 560, 760, 838, 760, 560, 320, 128]],
    (5, 1): [[1], [1, 1], [5, 2, 5], [25, 11, 11, 25], [125, 60, 62, 60, 125],
             [625, 325, 346, 346, 325, 625], [3125, 1750, 1915, 1972, 1915, 1750, 3125],
             [15625, 9375, 10525, 11131, 11131, 10525, 9375, 15625],
             [78125, 50000, 57500, 62320, 63982, 62320, 57500, 50000, 78125]],
}

def numerators(N, a, b, method=pmf_B):
    """Kagey's numerators for p = a/(a+b): 2 (a+b)^(N-1) P_N(k), and 1 for N = 0"""
    if N == 0:
        return [1]
    pm = method(N, F(a, a + b))
    out = [x * 2 * (a + b)**(N - 1) for x in pm]
    assert all(x.denominator == 1 for x in out)
    return [int(x) for x in out]

ok = all(numerators(N, a, b) == FIG[(a, b)][N] for (a, b) in FIG for N in range(9))
report("4. numerator tables of the figure, p = 1/3, 2/3, 5/6, rows 1..9", ok)

# ---- check 5: numerators = sum over words of a^(repeats) b^(changes)
ok = True
for (a, b) in [(1, 2), (2, 1), (5, 1), (3, 4), (7, 2)]:
    for N in range(1, NBRUTE + 1):
        direct = [0] * (N + 1)
        for (k, j), c in brute_W[N].items():
            direct[k] += c * a**(N - 1 - j) * b**j
        if direct != numerators(N, a, b):
            ok = False
report("5. numerators = sum_w a^repeats b^changes (enumeration), N<=%d" % NBRUTE, ok)

# bivariate generating function of the numerators
ok = True
for (a, b) in [(1, 2), (2, 1), (5, 1), (3, 4), (7, 2)]:
    n = {(0, 0): 1}
    for N in range(1, NBRUTE + 1):
        for (k, j), c in brute_W[N].items():
            n[(k, N - k)] = n.get((k, N - k), 0) + c * a**(N - 1 - j) * b**j
    den = {(0, 0): 1, (1, 0): -a, (0, 1): -a, (1, 1): a * a - b * b}
    num = {(0, 0): 1, (1, 0): -(a - 1), (0, 1): -(a - 1), (1, 1): (a - b) * (a + b - 2)}
    for x in range(NBRUTE + 1):
        for y in range(NBRUTE + 1 - x):
            lhs = sum(cf * n.get((x - i, y - l), 0) for (i, l), cf in den.items())
            if lhs != num.get((x, y), 0):
                ok = False
report("5b. numerator g.f. (1-(a-1)(x+y)+(a-b)(a+b-2)xy)/(1-a(x+y)+(a^2-b^2)xy), deg<=%d" % NBRUTE, ok)

# ---- check 6: A035002 (rook paths) = p = 2/3 table
A035002 = [1,1,1,2,2,2,4,5,5,4,8,12,14,12,8,16,28,37,37,28,16,32,64,94,106,94,64,32,64,144,232,289,
           289,232,144,64,128,320,560,760,838,760,560,320,128,256,704,1328,1944,2329,2329,1944,1328,
           704,256,512,1536,3104,4864,6266]
flat = []
N = 0
while len(flat) < len(A035002):
    flat.extend(numerators(N, 2, 1, pmf_A)); N += 1
report("6a. p=2/3 numerators = A035002 data (%d terms)" % len(A035002), flat[:len(A035002)] == A035002)

ROOK = 24
rook = [[0] * (ROOK + 1) for _ in range(ROOK + 1)]
rook[0][0] = 1
for x in range(ROOK + 1):
    for y in range(ROOK + 1):
        if x or y:
            rook[x][y] = sum(rook[i][y] for i in range(x)) + sum(rook[x][i] for i in range(y))
ok = all(numerators(N, 2, 1)[k] == rook[k][N - k] for N in range(ROOK + 1) for k in range(N + 1))
report("6b. p=2/3 numerators = rook-path counts by DP on the board, N<=%d" % ROOK, ok)

# ---- check 7: A348595 (walks avoiding (1,1),(2,2) mod 3) = p = 1/3 table
A348595 = [1,1,4,1,8,28,1,12,64,212,1,16,116,520,1676,1,20,184,1052,4288,13604,1,24,268,1872,9316,
           35784,112380,1,28,368,3044,17976,81708,301440,940020,1,32,484,4632,31740,167376,713940,
           2558280,7936620,1,36,616,6700,52336,314932,1531000,6231100,21842560,67494980]
tri = []
for n in range(10):
    for k in range(n + 1):
        tri.append(numerators(n + k, 1, 2, pmf_A)[k])
report("7a. p=1/3 numerators T(n,k)=row n+k, bin k = A348595 data (%d terms)" % len(A348595), tri == A348595)

BLK = 12
M = 3 * BLK
walk = [[0] * (M + 1) for _ in range(M + 1)]
for x in range(M + 1):
    for y in range(M + 1):
        if x % 3 == y % 3 and x % 3 != 0:
            continue
        if x == 0 and y == 0:
            walk[x][y] = 1
        else:
            walk[x][y] = (walk[x - 1][y] if x else 0) + (walk[x][y - 1] if y else 0)
ok = all(numerators(n + k, 1, 2)[k] == walk[3 * n][3 * k] for n in range(BLK + 1) for k in range(BLK + 1))
report("7b. p=1/3 numerators = blocked-lattice walk counts by DP, n,k<=%d" % BLK, ok)

# ---- check 8: three-term recurrence (a polynomial identity in p of degree <= 16, checked at 20 points)
ok = True
for p in GRID:
    rho = 2 * p - 1
    rows = [pmf_C(N, p) for N in range(NBRUTE + 1)]
    for N in range(2, NBRUTE + 1):
        for k in range(N + 1):
            up = (rows[N - 1][k] if k <= N - 1 else 0) + (rows[N - 1][k - 1] if k >= 1 else 0)
            upup = rows[N - 2][k - 1] if 1 <= k <= N - 1 else 0
            if rows[N][k] != p * up - rho * upup:
                ok = False
report("8. P_N(k) = p(P_{N-1}(k)+P_{N-1}(k-1)) - (2p-1)P_{N-2}(k-1), 2<=N<=%d" % NBRUTE, ok)

# ---- check 9: generating function for d directions, d = 2, 3, against enumeration
def series_check(d, p, xs, NN):
    """coefficients of t^0..t^NN of both sides of  G * Den = Num  at the point x = xs"""
    q = 1 - p
    sig = p - q / (d - 1)
    # brute force G_N(xs) = sum over words of prob * prod x_i^(count)
    G = [F(1)]
    for N in range(1, NN + 1):
        tot = F(0)
        for w in product(range(d), repeat=N):
            pr = F(1, d)
            for i in range(N - 1):
                pr *= p if w[i] == w[i + 1] else q / (d - 1)
            for c in w:
                pr *= xs[c]
            tot += pr
        G.append(tot)
    # polynomials in t as coefficient lists
    def mul(u, v):
        out = [F(0)] * (len(u) + len(v) - 1)
        for i, a in enumerate(u):
            for j, b in enumerate(v):
                out[i + j] += a * b
        return out
    def add(u, v):
        n = max(len(u), len(v))
        return [(u[i] if i < len(u) else 0) + (v[i] if i < len(v) else 0) for i in range(n)]
    Pi = [F(1)]
    for x in xs:
        Pi = mul(Pi, [F(1), -sig * x])
    # A * Pi = sum_i x_i t prod_{l != i} (1 - sig x_l t)
    APi = [F(0)]
    for i in range(d):
        term = [F(0), xs[i]]
        for l in range(d):
            if l != i:
                term = mul(term, [F(1), -sig * xs[l]])
        APi = add(APi, term)
    den = add(Pi, [-(q / (d - 1)) * c for c in APi])          # Pi (1 - q A/(d-1))
    num = add(den, [c / d for c in APi])                        # Pi (1 - q A/(d-1) + A/d)
    lhs = mul(G, den)
    return all(lhs[n] == (num[n] if n < len(num) else 0) for n in range(NN + 1))

ok = True
for p in [F(1, 3), F(2, 3), F(5, 6), F(1, 5), F(0), F(1)]:
    ok &= series_check(2, p, [F(3, 7), F(1)], 12)
    ok &= series_check(2, p, [F(-5, 3), F(2, 9)], 12)
    ok &= series_check(3, p, [F(3, 7), F(1), F(-2, 5)], 8)
    ok &= series_check(3, p, [F(2), F(1, 3), F(5, 4)], 8)
report("9. rational generating function, d = 2 (N<=12) and d = 3 (N<=8), enumeration", ok)

# d = 2 specialization: Den = 1 - p(1+x)t + (2p-1)x t^2, Num = 1 - (p-1/2)(1+x)t
ok = True
for p in GRID:
    x = F(3, 7)
    rows = [pmf_C(N, p) for N in range(NBRUTE + 1)]
    G = [sum(r[k] * x**k for k in range(len(r))) for r in rows]
    den = [F(1), -p * (1 + x), (2 * p - 1) * x]
    num = [F(1), -(p - F(1, 2)) * (1 + x)]
    for n in range(NBRUTE + 1):
        lhs = sum(G[n - i] * den[i] for i in range(3) if n - i >= 0)
        if lhs != (num[n] if n < 2 else 0):
            ok = False
report("10. G(x,t) = (1-(p-1/2)(1+x)t)/(1-p(1+x)t+(2p-1)xt^2), N<=%d" % NBRUTE, ok)

# ---- check 11: mean and variance of the bin index
def var_formula(N, p):
    if p == 1:
        return F(N * N, 4)
    rho = 2 * p - 1
    return (N * (1 + rho) / (1 - rho) - 2 * rho * (1 - rho**N) / (1 - rho)**2) / 4

ok = True
for p in GRID:
    for N in list(range(1, NBRUTE + 1)) + [25, 40]:
        pm = pmf_C(N, p) if N <= NBRUTE else pmf_B(N, p)
        mean = sum(k * pm[k] for k in range(N + 1))
        var = sum(k * k * pm[k] for k in range(N + 1)) - mean**2
        if mean != F(N, 2) or var != var_formula(N, p):
            ok = False
        if p != 1:
            alt = N * p / (4 * (1 - p)) - (2 * p - 1) * (1 - (2 * p - 1)**N) / (8 * (1 - p)**2)
            if alt != var:
                ok = False
report("11. mean N/2 and exact variance formula (both forms), N<=%d and N=25,40" % NBRUTE, ok)

# ---- check 12: covariance of the count vector for d = 3 (tetrahedral board)
ok = True
d = 3
for p in [F(1, 3), F(2, 3), F(5, 6), F(1, 5), F(0)]:
    q = 1 - p
    sig = p - q / (d - 1)
    for N in range(1, 10):
        E1 = [F(0)] * d
        E2 = [[F(0)] * d for _ in range(d)]
        for w in product(range(d), repeat=N):
            pr = F(1, d)
            for i in range(N - 1):
                pr *= p if w[i] == w[i + 1] else q / (d - 1)
            cnt = [w.count(c) for c in range(d)]
            for a in range(d):
                E1[a] += pr * cnt[a]
                for b in range(d):
                    E2[a][b] += pr * cnt[a] * cnt[b]
        v = N * (1 + sig) / (1 - sig) - 2 * sig * (1 - sig**N) / (1 - sig)**2
        for a in range(d):
            for b in range(d):
                cov = E2[a][b] - E1[a] * E1[b]
                if cov != v * (F(int(a == b), d) - F(1, d * d)):
                    ok = False
report("12. d=3: Cov(K_a,K_b) = v_N(sigma) (delta_ab/3 - 1/9), enumeration, N<=9", ok)

# ---- check 13 (float): characteristic function = c+ lam+^(N-1) + c- lam-^(N-1); |lam| < 1 off pi Z
ok = True
for p in [1 / 3, 2 / 3, 5 / 6]:
    q = 1 - p
    pf = F(p).limit_denominator(1000)
    for th in [0.05, 0.2, 0.31, 0.9, 1.5, 2.0, 3.0]:
        s_ = cmath.sqrt(q * q - (p * cmath.sin(th))**2)
        lp, lm = p * cmath.cos(th) + s_, p * cmath.cos(th) - s_
        if not (abs(lp) < 1 and abs(lm) < 1):
            ok = False
        phi2 = p * cmath.cos(2 * th) + q
        cp = (phi2 - lm * cmath.cos(th)) / (lp - lm)
        cm = cmath.cos(th) - cp
        for N in [1, 2, 3, 7, 12, 16]:
            pm = pmf_C(N, pf)
            phi = sum(float(pm[k]) * cmath.exp(1j * th * (2 * k - N)) for k in range(N + 1))
            if abs(phi - (cp * lp**(N - 1) + cm * lm**(N - 1))) > 1e-12:
                ok = False
report("13. (float) characteristic function eigenvalue formula, N<=16", ok)

# ---- check 14 (float): distance to the normal law with variance N p/(4(1-p)) at N = 2000
def pmf_float(N, p):
    q = 1 - p
    R = [0.0, 0.5]
    L = [0.5, 0.0]
    for n in range(2, N + 1):
        R2 = [0.0] * (n + 1)
        L2 = [0.0] * (n + 1)
        for k in range(n + 1):
            if k >= 1:
                R2[k] = p * R[k - 1] + q * L[k - 1]
            if k <= n - 1:
                L2[k] = p * L[k] + q * R[k]
        R, L = R2, L2
    return [R[k] + L[k] for k in range(N + 1)]

def pmf_float_rec(N, p):
    """same pmf from the three-term recurrence of check 8"""
    rho = 2 * p - 1
    prev2, prev = [1.0], [0.5, 0.5]
    for n in range(2, N + 1):
        cur = [0.0] * (n + 1)
        for k in range(n + 1):
            up = (prev[k] if k <= n - 1 else 0.0) + (prev[k - 1] if k >= 1 else 0.0)
            upup = prev2[k - 1] if 1 <= k <= n - 1 else 0.0
            cur[k] = p * up - rho * upup
        prev2, prev = prev, cur
    return prev

ok = True
dists = []
for p in [1 / 3, 2 / 3, 5 / 6]:
    N = 2000
    pm = pmf_float(N, p)
    pm2 = pmf_float_rec(N, p)
    if max(abs(x - y) for x, y in zip(pm, pm2)) > 1e-12:
        ok = False
    sd = sqrt(N * p / (4 * (1 - p)))
    cdf = 0.0
    worst = 0.0
    for k in range(N + 1):
        cdf += pm[k]
        z = (k + 0.5 - N / 2) / sd
        worst = max(worst, abs(cdf - 0.5 * (1 + erf(z / sqrt(2)))))
    dists.append(worst)
    if worst > 2e-4:
        ok = False
report("14. (float) sup |CDF - normal CDF| at N=2000, p=1/3,2/3,5/6", ok,
       "(" + ", ".join("%.2e" % x for x in dists) + ")")

# ---------------------------------------------------------------- middle = extremes
def S_coeffs(N):
    k = N // 2
    return [W(N, k, j) for j in range(N)]          # S_N(u) = sum_j coeff[j] u^j, coeff[0] = 0

PREC = 64
def u_root(N, jmax=500):
    """largest a with S_N(a/2^PREC) < 1, by bisection in exact integer arithmetic.
    For N > jmax the polynomial is truncated at degree jmax; the dropped terms are positive and
    smaller than 1e-100 on the search range (checked below)."""
    c = S_coeffs(N)[:jmax + 1]
    J = len(c) - 1
    one = 1 << (PREC * J)
    def horner(a):
        tot = 0
        for j in range(J, 0, -1):
            tot = tot * a + (c[j] << (PREC * (J - j)))
        return tot * a >= one                       # sum_j c_j a^j 2^(PREC (J-j)) >= 2^(PREC J)
    lo, hi = 0, 1 << PREC
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if horner(mid):
            hi = mid
        else:
            lo = mid
    return F(lo, 1 << PREC)

# exact small cases
ok = (pmf_A(2, F(2, 3))[1] == pmf_A(2, F(2, 3))[0])
p = F(7071067811, 10**10)
ok &= pmf_C(3, p)[1] > pmf_C(3, p)[0] and pmf_C(3, p + F(1, 10**10))[1] < pmf_C(3, p + F(1, 10**10))[0]
xs = [F(i, 97) for i in range(98)]
ok &= all(pmf_C(3, x)[1] - pmf_C(3, x)[0] == (1 - 2 * x * x) / 2 for x in xs)
ok &= all(pmf_C(4, x)[2] - pmf_C(4, x)[0] == (1 - x) * (1 - x + x * x) - x**3 / 2 for x in xs)
report("15. p_2 = 2/3; P_3(mid)-P_3(0) = (1-2p^2)/2; P_4(2)-P_4(0) = (1-p)(1-p+p^2)-p^3/2", ok)

# coefficientwise domination S_N <= S_{N+1} (the mechanism behind monotonicity of p_N)
ok = True
for N in range(2, 301):
    c0, c1 = S_coeffs(N) + [0], S_coeffs(N + 1)
    if not all(c1[j] >= c0[j] for j in range(N)) or not c1[2] > c0[2]:
        ok = False
report("16. W(N+1,mid,j) >= W(N,mid,j) for all j, strict at j=2, 2<=N<=300", ok)

# table of p_N: method 1 = root of S_N (closed form), method 2 = sign change of the DP pmf
TABLE_N = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 20, 50, 100, 200, 400]
roots = {}
ok = True
print("    N  row    p_N            N(1-p_N)/log N")
for N in TABLE_N:
    u = u_root(N)
    pN = 1 / (1 + u)
    roots[N] = pN
    lo = F(int(pN * 10**10), 10**10)
    hi = lo + F(1, 10**10)
    dlo = pmf_B(N, lo); dhi = pmf_B(N, hi)
    good = dlo[N // 2] > dlo[0] and dhi[N // 2] < dhi[0]
    ok &= good
    print("  %4d %4d   %.10f   %.4f   %s" % (N, N + 1, float(lo), N * (1 - float(pN)) / log(N),
                                             "" if good else "DP sign check failed"))
report("17. p_N: root of S_N (closed form) bracketed to 1e-10 by DP sign change, N<=400", ok)

# uniqueness on a grid: P_N(mid) - P_N(0) changes sign exactly once on [0,1]
ok = True
for N in range(2, 15):
    signs = []
    for i in range(0, 201):
        pm = pmf_C(N, F(i, 200))
        diff = pm[N // 2] - pm[0]
        signs.append(diff > 0)
    changes = sum(1 for i in range(200) if signs[i] != signs[i + 1])
    if changes != 1 or not signs[0] or signs[-1]:
        ok = False
report("18. middle - extreme changes sign exactly once on the grid p = i/200, 2<=N<=14", ok)

# monotonicity of p_N
seq = [u_root(N) for N in range(2, 122)]
report("19. p_N strictly increasing for 2<=N<=121", all(seq[i] > seq[i + 1] for i in range(len(seq) - 1)))

# large N: truncation is harmless, float DP as second method, Bessel heuristic
def bessel_x(m):
    """root of 2x(I0(2x)+I1(2x)) = m, power series and bisection"""
    def G(x):
        i0 = sum(x**(2 * i) / factorial(i)**2 for i in range(80))
        i1 = sum(x**(2 * i + 1) / (factorial(i) * factorial(i + 1)) for i in range(80))
        return 2 * x * (i0 + i1)
    lo, hi = 0.0, 20.0
    for _ in range(100):
        mid = (lo + hi) / 2
        if G(mid) < m:
            lo = mid
        else:
            hi = mid
    return lo

def bessel_x2(m):
    """same root, I_n(z) = (1/pi) int_0^pi exp(z cos t) cos(nt) dt by the midpoint rule, and secant"""
    from math import cos, exp, pi
    def G(x):
        n = 4000
        tot = 0.0
        for i in range(n):
            t = (i + 0.5) * pi / n
            tot += exp(2 * x * cos(t)) * (1 + cos(t))
        return 2 * x * tot / n
    x0, x1 = 0.5, 4.0
    f0, f1 = log(G(x0) / m), log(G(x1) / m)
    for _ in range(60):
        if abs(f1) < 1e-14 or f1 == f0:
            break
        x0, x1, f0 = x1, x1 - f1 * (x1 - x0) / (f1 - f0), f1
        f1 = log(G(x1) / m)
    return x1

ok = True
okb = True
print("    N     1-p_N        N(1-p_N)/log N   u_Bessel/u_N")
for N, window in [(800, (0.9950, 0.9970)), (1600, (0.9970, 0.9985)), (3200, (0.9983, 0.9992))]:
    u = u_root(N)
    c = S_coeffs(N)
    uf = float(u) * 1.01
    tail = sum(float(F(c[j])) * uf**j if c[j] < 10**300 else float(F(c[j]) * F(uf)**j) for j in range(501, 560))
    if not tail < 1e-100:
        ok = False
    pN = 1 / (1 + u)
    lo = float(pN) - 5e-9
    hi = float(pN) + 5e-9
    dlo = pmf_float(N, lo); dhi = pmf_float(N, hi)
    if not (dlo[N // 2] > dlo[0] and dhi[N // 2] < dhi[0]):
        ok = False
    ub = bessel_x(N / 2) / (N / 2)
    ratio = ub / float(u)
    if not (window[0] <= ratio <= window[1] and ratio < 1):
        okb = False
    print("  %5d   %.8f   %.4f           %.5f" % (N, 1 - float(pN), N * (1 - float(pN)) / log(N), ratio))
small = []
for N in (100, 200, 400):
    small.append(bessel_x(N / 2) / (N / 2) / float((1 - roots[N]) / roots[N]))
print("  Bessel ratio at N=100,200,400: " + ", ".join("%.4f" % r for r in small))
okx = all(abs(bessel_x(N / 2) - bessel_x2(N / 2)) < 1e-9 for N in (100, 200, 400, 800, 1600, 3200))
report("20. Bessel root x_B: series+bisection = quadrature+secant", okx)
report("21. p_N for N=800,1600,3200: root of S_N bracketed to 1e-8 by float DP", ok)
report("22. ledger H2: Bessel ratio inside the registered windows", okb)

print("=" * 80)
print("%d checks, %d failed, %.1fs" % (len(results), results.count(False), time.time() - t0))
sys.exit(0 if all(results) else 1)
