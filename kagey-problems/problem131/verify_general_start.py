"""Checks for the Paper B notes on the complete-graph tie, the general start law, and the
Kirchhoff (spanning-tree) form of the constants a_k.

Standard library only (fractions, math, itertools, time). Predictions are registered in
data/ledger_B_tie.md before this script is run; the output goes to
data/general_start_output.txt.

Notation: d states, repeat probability p, switch probability r = (1-p)/(d-1) to each other
state, sigma = p - r, u = r/p, v = r/sigma = u/(1-u), z = N u, L = log N,
window coordinate t = z - L + (1/2) log L. Start law mu.

Three independent ways of computing bin probabilities are used:
  M1  the general-start refresh formula
      P = sum_m (sum_i mu_i m_i) (M-1)!/prod m_i! r^{M-1} sigma^{N-M} prod C(n_i-1, m_i-1),
  M2  the start-resolved run formula
      P/p^{N-1} = sum_a mu_a S^(a)_n(u),  S^(a) = sum_m E(m,a) prod C(n_i-1,m_i-1) u^{M-1},
      E(m,a) = number of Smirnov words (no two equal neighbours) with multiplicities m that
      start with a,
  M3  brute force (enumeration of words, or a forward dynamic program over positions).
"""
import itertools
import math
import sys
import time
from fractions import Fraction as Fr

LOG4PI = math.log(4 * math.pi)
OUT = []


def say(*a):
    s = " ".join(str(x) for x in a)
    OUT.append(s)
    print(s, flush=True)


def a_const(k):
    return 0.5 * LOG4PI - (k + 0.5) / (k - 1) * math.log(k)


# ----------------------------------------------------------------------------------------
# exact linear algebra
# ----------------------------------------------------------------------------------------
def det_frac(A):
    A = [row[:] for row in A]
    n = len(A)
    det = Fr(1)
    for c in range(n):
        piv = None
        for r_ in range(c, n):
            if A[r_][c] != 0:
                piv = r_
                break
        if piv is None:
            return Fr(0)
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            det = -det
        det *= A[c][c]
        for r_ in range(c + 1, n):
            f = A[r_][c] / A[c][c]
            if f:
                for cc in range(c, n):
                    A[r_][cc] -= f * A[c][cc]
    return det


def inv_frac(A):
    n = len(A)
    M = [row[:] + [Fr(int(i == j)) for j in range(n)] for i, row in enumerate(A)]
    for c in range(n):
        piv = next(r_ for r_ in range(c, n) if M[r_][c] != 0)
        M[c], M[piv] = M[piv], M[c]
        pv = M[c][c]
        M[c] = [x / pv for x in M[c]]
        for r_ in range(n):
            if r_ != c and M[r_][c] != 0:
                f = M[r_][c]
                M[r_] = [a - f * b for a, b in zip(M[r_], M[c])]
    return [row[n:] for row in M]


def det_float(A):
    A = [row[:] for row in A]
    n = len(A)
    det = 1.0
    for c in range(n):
        piv = max(range(c, n), key=lambda r_: abs(A[r_][c]))
        if A[piv][c] == 0:
            return 0.0
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            det = -det
        det *= A[c][c]
        for r_ in range(c + 1, n):
            f = A[r_][c] / A[c][c]
            for cc in range(c, n):
                A[r_][cc] -= f * A[c][cc]
    return det


# ----------------------------------------------------------------------------------------
# T1: Kirchhoff form of the constants
# ----------------------------------------------------------------------------------------
def tau_matrix_tree(c, k):
    """det of the Laplacian of conductances c (dict on pairs) with row/col 0 deleted."""
    Lap = [[Fr(0)] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            if i != j:
                Lap[i][j] = -c[(min(i, j), max(i, j))]
                Lap[i][i] += c[(min(i, j), max(i, j))]
    return det_frac([row[1:] for row in Lap[1:]])


def tau_pruefer(c, k):
    if k == 2:
        return c[(0, 1)]
    total = Fr(0)
    for seq in itertools.product(range(k), repeat=k - 2):
        deg = [1] * k
        for s in seq:
            deg[s] += 1
        w = Fr(1)
        seq = list(seq)
        for s in seq:
            leaf = min(i for i in range(k) if deg[i] == 1)
            w *= c[(min(leaf, s), max(leaf, s))]
            deg[leaf] -= 1
            deg[s] -= 1
        rest = [i for i in range(k) if deg[i] == 1]
        w *= c[(rest[0], rest[1])]
        total += w
    return total


def doob_sigma_det(x):
    """exact det Sigma for the Doob chain G_ij = x_j/x_i, alpha_i = x_i^2/sum x^2."""
    k = len(x)
    S = sum(xi * xi for xi in x)
    alpha = [xi * xi / S for xi in x]
    G = [[Fr(0)] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            if i != j:
                G[i][j] = x[j] / x[i]
        G[i][i] = -sum(G[i][j] for j in range(k) if j != i)
    for j in range(k):  # stationarity check
        assert sum(alpha[i] * G[i][j] for i in range(k)) == 0
    B = [[alpha[j] - G[i][j] for j in range(k)] for i in range(k)]
    Binv = inv_frac(B)
    Z = [[Binv[i][j] - alpha[j] for j in range(k)] for i in range(k)]
    Gam = [[alpha[i] * Z[i][j] + alpha[j] * Z[j][i] for j in range(k)] for i in range(k)]
    Sig = [row[1:] for row in Gam[1:]]
    return det_frac(Sig), alpha, S


def T1():
    say("=" * 90)
    say("T1  Kirchhoff form of the constants")
    say("-" * 90)
    say("(a) exp(-(k-1)a_k) against D_k = k^{k+1/2}/(4pi)^{(k-1)/2}")
    worst = 0.0
    for k in range(2, 8):
        a = a_const(k)
        Dk = k ** (k + 0.5) / (4 * math.pi) ** ((k - 1) / 2)
        e = math.exp(-(k - 1) * a)
        worst = max(worst, abs(e / Dk - 1))
        say(f"   k={k}  a_k={a:+.12f}  D_k={Dk:.12f}  exp(-(k-1)a_k)={e:.12f}"
            f"  D_k/k^{{k-2}}={Dk / k**(k-2):.6f} (= k^{{5/2}}(4pi)^{{-(k-1)/2}}"
            f" = {k**2.5/(4*math.pi)**((k-1)/2):.6f})")
    say(f"   worst relative difference {worst:.2e}")
    say("(b) tau(K_k, c_ij = x_i x_j): matrix-tree vs Pruefer enumeration vs prod x (sum x)^{k-2}")
    for k in range(2, 8):
        x = [Fr(i * i + 1, i + 2) for i in range(1, k + 1)]
        c = {(i, j): x[i] * x[j] for i in range(k) for j in range(i + 1, k)}
        t1 = tau_matrix_tree(c, k)
        t2 = tau_pruefer(c, k)
        prodx = Fr(1)
        for xi in x:
            prodx *= xi
        t3 = prodx * sum(x) ** (k - 2)
        # unit weights: Cayley
        cu = {key: Fr(1) for key in c}
        cay = tau_matrix_tree(cu, k)
        say(f"   k={k}: matrix-tree==Pruefer: {t1 == t2}   ==closed form: {t1 == t3}"
            f"   unit-weight count {cay} (k^(k-2) = {k**(k-2)})  trees enumerated {k**(k-2)}")
    say("(c) det Sigma(Doob chain) == 2^{k-1} (prod alpha)^2 / tau(sqrt(alpha_i alpha_j)), exact")
    for k in range(2, 8):
        x = [Fr(2 * i + 1, i + 3) for i in range(k)]
        dS, alpha, S = doob_sigma_det(x)
        c = {(i, j): x[i] * x[j] / S for i in range(k) for j in range(i + 1, k)}
        tau = tau_pruefer(c, k)
        pa = Fr(1)
        for al in alpha:
            pa *= al
        rhs = Fr(2) ** (k - 1) * pa * pa / tau
        say(f"   k={k}: equal: {dS == rhs}   det Sigma = {float(dS):.6e}")
    say("   center of K_k (x all equal): det Sigma_k == 2^{k-1} k^{1-2k}:")
    for k in range(2, 8):
        dS, _, _ = doob_sigma_det([Fr(1)] * k)
        say(f"      k={k}: {dS == Fr(2) ** (k - 1) / Fr(k) ** (2 * k - 1)}")
    say("(d) D(alpha): Paper B's form vs A^2 (4pi)^{-(k-1)/2} sqrt(tau)/prod alpha"
        " vs A^2 det(2 pi Sigma)^{-1/2}")
    worst_b = worst_c = 0.0
    import random
    rng = random.Random(20260926)
    for k in range(2, 8):
        for _ in range(5):
            x = [Fr(rng.randint(1, 40), rng.randint(1, 40)) for _ in range(k)]
            dS, alpha, S = doob_sigma_det(x)
            af = [float(a_) for a_ in alpha]
            A = sum(math.sqrt(a_) for a_ in af)
            pa = math.prod(af)
            DB = A ** (k / 2 + 1) * pa ** (-0.75) / (4 * math.pi) ** ((k - 1) / 2)
            tau = math.prod(math.sqrt(a_) for a_ in af) * A ** (k - 2)
            Dtree = A * A * (4 * math.pi) ** (-(k - 1) / 2) * math.sqrt(tau) / pa
            Dcov = A * A * ((2 * math.pi) ** (k - 1) * float(dS)) ** -0.5
            worst_b = max(worst_b, abs(Dtree / DB - 1))
            worst_c = max(worst_c, abs(Dcov / DB - 1))
    say(f"   35 random alpha: worst rel diff tree form {worst_b:.2e}, covariance form {worst_c:.2e}")
    say("(e) Legendre check: det Hess_{alpha'} (d - A^2) * det Sigma_alpha = 1")
    worst = 0.0
    for k in range(2, 6):
        for trial in range(3):
            x = [Fr(rng.randint(10, 20), rng.randint(10, 20)) for _ in range(k)]
            dS, alpha, S = doob_sigma_det(x)
            a0 = [float(a_) for a_ in alpha[1:]]

            def I(ap):
                a1 = 1 - sum(ap)
                return -(math.sqrt(a1) + sum(math.sqrt(q) for q in ap)) ** 2

            h = 1e-4
            m = k - 1
            H = [[0.0] * m for _ in range(m)]
            for i in range(m):
                for j in range(m):
                    def sh(di, dj):
                        ap = a0[:]
                        ap[i] += di
                        ap[j] += dj
                        return I(ap)
                    H[i][j] = (sh(h, h) - sh(h, -h) - sh(-h, h) + sh(-h, -h)) / (4 * h * h)
            val = det_float(H) * float(dS)
            worst = max(worst, abs(val - 1))
            say(f"   k={k} alpha={[round(a_, 4) for a_ in map(float, alpha)]}: product = {val:.9f}")
    say(f"   worst |product - 1| = {worst:.2e}")
    say("(f) mass identity sum_n S_n(u) = sum_j (-1)^{k-j} C(k,j) j (1+(j-1)u)^{N-1}")
    allok = True
    for k in range(2, 5):
        for N in range(k, 10):
            coef = [0] * N
            for w in itertools.product(range(k), repeat=N):
                if len(set(w)) < k:
                    continue
                ch = sum(1 for i in range(N - 1) if w[i] != w[i + 1])
                coef[ch] += 1
            rhs = [0] * N
            for j in range(1, k + 1):
                sgn = (-1) ** (k - j)
                for e in range(N):
                    rhs[e] += sgn * math.comb(k, j) * j * math.comb(N - 1, e) * (j - 1) ** e
            if coef != rhs:
                allok = False
                say(f"   MISMATCH k={k} N={N}: {coef} vs {rhs}")
    say(f"   brute force (all k^N words) == closed form for k=2..4, N=k..9: {allok}")
    worst = 0.0
    for k in range(2, 8):
        Dk = k ** (k + 0.5) / (4 * math.pi) ** ((k - 1) / 2)
        detS = 2 ** (k - 1) * k ** (1 - 2 * k)
        val = Dk * (2 * math.pi) ** ((k - 1) / 2) * math.sqrt(detS)
        worst = max(worst, abs(val / k - 1))
    say(f"   D_k (2pi)^{{(k-1)/2}} sqrt(det Sigma_k) / k - 1: worst {worst:.2e} (k=2..7)")
    say("(g) Huang-Kious-Sidoravicius-Tarres Theorem 1 (last-exit trees) vs run-count density, K_3")
    hkst_check()


def bessel_I(n, x):
    n = abs(n)
    term = (x / 2) ** n / math.factorial(n)
    s = term
    kk = 0
    while True:
        kk += 1
        term *= (x / 2) ** 2 / (kk * (kk + n))
        s += term
        if term < 1e-18 * s:
            return s


_SMIR = {}


def smirnov_end_table(mm):
    """E[m1][m2][m3][c] for 3 colours: # words with multiplicities m, no equal neighbours,
    ending in colour c (floats). The last table is cached."""
    mm = tuple(mm)
    if mm in _SMIR:
        return _SMIR[mm]
    _SMIR.clear()
    M1, M2, M3 = mm
    E = {}
    for m1 in range(M1 + 1):
        for m2 in range(M2 + 1):
            for m3 in range(M3 + 1):
                m = (m1, m2, m3)
                if m1 + m2 + m3 == 0:
                    continue
                vals = [0.0, 0.0, 0.0]
                for c in range(3):
                    if m[c] == 0:
                        continue
                    prev = list(m)
                    prev[c] -= 1
                    prev = tuple(prev)
                    if sum(prev) == 0:
                        vals[c] = 1.0
                    else:
                        pv = E[prev]
                        vals[c] = sum(pv[cc] for cc in range(3) if cc != c)
                E[m] = vals
    _SMIR[mm] = E
    return E


def hkst_check():
    ell = [0.7, 1.1, 1.6]
    i0 = 0
    V = range(3)
    trees = [((0, 1), (1, 2)), ((0, 1), (0, 2)), ((0, 2), (1, 2))]
    cyc = {(0, 1): 1, (1, 2): 1, (2, 0): 1, (1, 0): -1, (2, 1): -1, (0, 2): -1}

    def orient(tree, root):
        adj = {i: [] for i in V}
        for (i, j) in tree:
            adj[i].append(j)
            adj[j].append(i)
        out = set()
        stack = [root]
        seen = {root}
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if y not in seen:
                    seen.add(y)
                    out.add((y, x))
                    stack.append(y)
        return out

    total = 0.0
    for i1 in V:
        a0 = {(i, j): 0 for i in V for j in V if i != j}
        if i1 != i0:
            a0[(i0, i1)] = 1
            a0[(i1, i0)] = -1
        for tree in trees:
            To = orient(tree, i1)
            for w in range(-40, 41):
                a = {e: a0[e] + w * cyc[e] for e in a0}
                at = {(i, j): a[(i, j)] - (1 if (i, j) in To else 0) + (1 if (j, i) in To else 0)
                      for (i, j) in a}
                adiv = [sum(at[(i, j)] for j in V if j != i) for i in V]
                term = math.exp(-sum(2 * l for l in ell))
                for (i, j) in [(0, 1), (0, 2), (1, 2)]:
                    term *= bessel_I(at[(i, j)], 2 * math.sqrt(ell[i] * ell[j]))
                for i in V:
                    term *= ell[i] ** (adiv[i] / 2)
                total += term
    mm = (40, 40, 40)
    E = smirnov_end_table(mm)
    H = 0.0
    for m, vals in E.items():
        if min(m) == 0:
            continue
        H += vals[i0] * math.prod(ell[i] ** (m[i] - 1) / math.factorial(m[i] - 1) for i in V)
    g = math.exp(-sum(2 * l for l in ell)) * H
    say(f"   HKST density = {total:.15e}   run-count density = {g:.15e}"
        f"   rel diff = {abs(total / g - 1):.2e}")


# ----------------------------------------------------------------------------------------
# general-start bin probabilities: brute force (exact)
# ----------------------------------------------------------------------------------------
def brute_bins(d, N, p, mu, start_only=None):
    """exact P(n) for all bins, by enumeration of words. Returns dict n -> Fraction."""
    r = (1 - p) / (d - 1)
    P = {}
    for w in itertools.product(range(d), repeat=N):
        if start_only is not None and w[0] != start_only:
            continue
        pr = mu[w[0]]
        if pr == 0:
            continue
        for i in range(N - 1):
            pr *= p if w[i] == w[i + 1] else r
        n = tuple(w.count(c) for c in range(d))
        P[n] = P.get(n, Fr(0)) + pr
    return P


def refresh_exact(n, N, p, mu, d):
    """exact general-start refresh formula (M1) for bin n (tuple of length d)."""
    r = (1 - p) / (d - 1)
    sigma = p - r
    H = [i for i in range(d) if n[i] > 0]
    ranges = [range(1, n[i] + 1) for i in H]
    tot = Fr(0)
    for ms in itertools.product(*ranges):
        M = sum(ms)
        wmu = sum(mu[H[j]] * ms[j] for j in range(len(H)))
        if wmu == 0:
            continue
        term = wmu * math.factorial(M - 1)
        for j in range(len(H)):
            term = term / math.factorial(ms[j]) * math.comb(n[H[j]] - 1, ms[j] - 1)
        term *= r ** (M - 1) * (sigma ** (N - M) if N - M > 0 else 1)
        tot += term
    return tot


def T2():
    say("=" * 90)
    say("T2  exact law with a general start")
    say("-" * 90)
    d = 3
    mu = [Fr(1, 2), Fr(1, 3), Fr(1, 6)]
    unif = [Fr(1, 3)] * 3
    ok_a = ok_b = ok_c = True
    nb = 0
    for p in [Fr(1, 5), Fr(1, 2), Fr(9, 10)]:
        for N in range(1, 8):
            B = brute_bins(d, N, p, mu)
            Bu = brute_bins(d, N, p, unif)
            for n, val in B.items():
                nb += 1
                if refresh_exact(n, N, p, mu, d) != val:
                    ok_a = False
                    say(f"   MISMATCH (a) p={p} N={N} n={n}")
            # (b) balanced bins
            for F in [(0, 1), (0, 2), (1, 2), (0, 1, 2)]:
                k = len(F)
                if N % k:
                    continue
                n = tuple(N // k if c in F else 0 for c in range(d))
                lhs = B.get(n, Fr(0))
                muF = sum(mu[c] for c in F)
                rhs = Fr(d) * muF / k * Bu.get(n, Fr(0))
                if lhs != rhs:
                    ok_b = False
                    say(f"   MISMATCH (b) p={p} N={N} n={n}")
            # (c) omega from refresh weights vs start-resolved enumeration (sigma > 0 only)
            if p > Fr(1, 3) and N >= 2:
                starts = [brute_bins(d, N, p, [Fr(1)] * 3, start_only=a) for a in range(d)]
                for n in B:
                    Hs = [i for i in range(d) if n[i] > 0]
                    tot = sum(starts[a].get(n, Fr(0)) for a in range(d))
                    r = (1 - p) / (d - 1)
                    v = r / (p - r)
                    num = [Fr(0)] * d
                    den = Fr(0)
                    for ms in itertools.product(*[range(1, n[i] + 1) for i in Hs]):
                        M = sum(ms)
                        w = Fr(math.factorial(M)) * v ** M
                        for j, i in enumerate(Hs):
                            w = w / math.factorial(ms[j]) * math.comb(n[i] - 1, ms[j] - 1)
                        den += w
                        for j, i in enumerate(Hs):
                            num[i] += w * Fr(ms[j], M)
                    for a in Hs:
                        if num[a] / den != starts[a].get(n, Fr(0)) / tot:
                            ok_c = False
                            say(f"   MISMATCH (c) p={p} N={N} n={n} a={a}")
    say(f"(a) refresh formula == enumeration for {nb} bins (d=3, mu=(1/2,1/3,1/6),"
        f" p in {{1/5,1/2,9/10}}, N=1..7): {ok_a}")
    say(f"(b) balanced bins, k | N: P^mu == (d mu(F)/k) P^unif exactly: {ok_b}")
    say(f"(c) omega_a = E_w[m_a/M] (refresh weights) == S^(a)/S (enumeration): {ok_c}")
    say("(d) rounding, k=2, bin (h+1,h) at t=0 (z = L - (1/2) log L + a_2)")
    for N in [21, 201, 2001]:
        L = math.log(N)
        z = L - 0.5 * math.log(L) + a_const(2)
        u = z / N
        h = N // 2
        nb_, ns_ = h + 1, h
        # method 2: 2-colour run formula S^(a)
        S_big = two_colour_start(nb_, ns_, u)
        S_small = two_colour_start(ns_, nb_, u)
        om_big2 = S_big / (S_big + S_small)
        # method 1: refresh weights
        om_big1, EM, EM2 = refresh_omega(nb_, ns_, u)
        diff = 2 * om_big1 - 1
        bound = (2 / h) * (EM + EM2)
        say(f"   N={N}: omega_big (refresh)={om_big1:.15f} (run)={om_big2:.15f}"
            f"  N(omega_big-omega_small)={N*diff:.6f}  proved bound (2/h)(EM+EM^2)={bound:.4e}"
            f"  diff<=bound: {diff <= bound}  heuristic 0.5(1-1/(4z))={0.5*(1-1/(4*z)):.4f}")
    say("(e) omega lemma, k=2, n=(1200,800), N=2000, z = L - (1/2) log L")
    N = 2000
    L = math.log(N)
    z = L - 0.5 * math.log(L)
    u = z / N
    S1 = two_colour_start(1200, 800, u)
    S2 = two_colour_start(800, 1200, u)
    om1, _, _ = refresh_omega(1200, 800, u)
    tgt = math.sqrt(.6) / (math.sqrt(.6) + math.sqrt(.4))
    say(f"   omega_1 (run)={S1/(S1+S2):.12f} (refresh)={om1:.12f}  limit sqrt(a1)/A={tgt:.6f}"
        f"  diff={om1-tgt:+.5f}  heuristic (1-2 sqrt(a1)/A)/(4A^2 z)="
        f"{(1-2*tgt)/(4*(math.sqrt(.6)+math.sqrt(.4))**2*z):+.5f}")


def two_colour_start(na, nb, u):
    """S^(a)(u) for two colours, counts (na, nb), words starting with colour a (floats,
    scaled: returns S^(a)(u) exactly up to rounding)."""
    # runs alternate a,b,a,... ; ma = mb or ma = mb+1
    s = 0.0
    # g(n, m) = C(n-1, m-1) u^(m-1) by ratio recursion
    def gl(n, mmax):
        g = [0.0] * (mmax + 2)
        g[1] = 1.0
        for m in range(1, mmax + 1):
            g[m + 1] = g[m] * (n - m) / m * u if m < n else 0.0
        return g
    mmax = min(max(na, nb), 400)
    ga, gb = gl(na, mmax), gl(nb, mmax)
    for mb in range(0, mmax):
        for ma in (mb, mb + 1):
            if ma < 1 or ma > min(na, mmax) or (mb > min(nb, mmax)):
                continue
            if mb == 0:
                continue  # both colours must appear
            s += ga[ma] * gb[mb] * u  # u^{(ma-1)+(mb-1)+1} = u^{ma+mb-1}
    return s


def refresh_omega(na, nb, u):
    """omega_a = E_w[m_a/M], w(m) prop to M!/(ma! mb!) v^M C(na-1,ma-1) C(nb-1,mb-1);
    also returns E_w M and E_w M^2."""
    v = u / (1 - u)
    mmax = min(max(na, nb), 400)
    la = [None] * (mmax + 1)
    lb = [None] * (mmax + 1)
    # log weights
    def logc(n, m):
        return math.lgamma(n) - math.lgamma(m) - math.lgamma(n - m + 1)
    terms = []
    for ma in range(1, min(na, mmax) + 1):
        for mb in range(1, min(nb, mmax) + 1):
            M = ma + mb
            lw = (math.lgamma(M + 1) - math.lgamma(ma + 1) - math.lgamma(mb + 1)
                  + M * math.log(v) + logc(na, ma) + logc(nb, mb))
            terms.append((lw, ma, M))
    mx = max(t[0] for t in terms)
    Z = s1 = sM = sM2 = 0.0
    for lw, ma, M in terms:
        w = math.exp(lw - mx)
        Z += w
        s1 += w * ma / M
        sM += w * M
        sM2 += w * M * M
    return s1 / Z, sM / Z, sM2 / Z


# ----------------------------------------------------------------------------------------
# fast float evaluators for general faces (M1 and M2)
# ----------------------------------------------------------------------------------------
_PASCAL = {}


def pascal_row(M):
    if M not in _PASCAL:
        _PASCAL[M] = [float(math.comb(M, j)) for j in range(M + 1)]
    return _PASCAL[M]


def beta_list(n, N, mmax):
    """beta(m) = C(n-1, m-1)/N^{m-1}, m = 1..min(n, mmax); index 0 unused (0.0)."""
    top = min(n, mmax)
    b = [0.0] * (top + 1)
    b[1] = 1.0
    for m in range(1, top):
        b[m + 1] = b[m] * (n - m) / (m * N)
    return b


def egf_conv(f, g):
    out = [0.0] * (len(f) + len(g) - 1)
    for M in range(len(out)):
        row = pascal_row(M) if M < 1030 else None
        s = 0.0
        jlo = max(0, M - len(g) + 1)
        jhi = min(M, len(f) - 1)
        for j in range(jlo, jhi + 1):
            fj = f[j]
            if fj:
                gg = g[M - j]
                if gg:
                    s += row[j] * fj * gg
        out[M] = s
    return out


def m1_coeffs(n, N, mu, mmax):
    """R_M with P^mu(n)/p^{N-1} = (1+v)^{-(N-1)} v^{k-1} sum_M R_M y^{M-k}, y = N v."""
    k = len(n)
    betas = [beta_list(ni, N, mmax) for ni in n]
    tot = None
    for i in range(k):
        if mu[i] == 0:
            continue
        bt = [m * b for m, b in enumerate(betas[i])]
        acc = bt
        for j in range(k):
            if j != i:
                acc = egf_conv(acc, betas[j])
        acc = [mu[i] * a for a in acc]
        tot = acc if tot is None else [a + b for a, b in zip(tot, acc)]
    return [0.0] + [tot[M] / M for M in range(1, len(tot))]


def m1_logratio(R, k, N, u):
    """log of P^mu(n)/p^{N-1} from the coefficients R (M1)."""
    v = u / (1 - u)
    y = N * v
    return -(N - 1) * math.log1p(v) + (k - 1) * math.log(v) + _logpoly(R, k, y)


def _logpoly(R, k, y):
    """log sum_{M>=k} R_M y^{M-k} for R_M >= 0, computed with log-sum-exp."""
    ly = math.log(y)
    logs = [math.log(R[M]) + (M - k) * ly for M in range(k, len(R)) if R[M] > 0]
    mx = max(logs)
    return mx + math.log(sum(math.exp(x - mx) for x in logs))


def m2_coeffs(n, N, mu, mmax):
    """C_M with sum_a mu_a S^(a)(u) = u^{k-1} sum_M C_M z^{M-k}, z = N u (M2), k = 2 or 3."""
    k = len(n)
    betas = [beta_list(ni, N, mmax) for ni in n]
    tops = [len(b) - 1 for b in betas]
    C = [0.0] * (sum(tops) + 1)
    if k == 2:
        for m1 in range(1, tops[0] + 1):
            for m2 in (m1 - 1, m1, m1 + 1):
                if 1 <= m2 <= tops[1]:
                    # E_start(m, a): alternating words; start with a possible iff m_a >= m_other
                    e0 = 1.0 if m1 >= m2 else 0.0
                    e1 = 1.0 if m2 >= m1 else 0.0
                    C[m1 + m2] += (mu[0] * e0 + mu[1] * e1) * betas[0][m1] * betas[1][m2]
        return C
    E = smirnov_end_table(tuple(tops))
    for m1 in range(1, tops[0] + 1):
        b1 = betas[0][m1]
        for m2 in range(1, tops[1] + 1):
            b12 = b1 * betas[1][m2]
            for m3 in range(1, tops[2] + 1):
                e = E[(m1, m2, m3)]
                w = mu[0] * e[0] + mu[1] * e[1] + mu[2] * e[2]
                C[m1 + m2 + m3] += w * b12 * betas[2][m3]
    return C


def m2_logratio(C, k, N, u):
    z = N * u
    return (k - 1) * math.log(u) + _logpoly(C, k, z)


def bisect_root(f, lo, hi, it=200, tol=1e-15):
    flo, fhi = f(lo), f(hi)
    assert flo < 0 < fhi, (flo, fhi)
    for _ in range(it):
        mid = 0.5 * (lo + hi)
        fm = f(mid)
        if fm < 0:
            lo = mid
        else:
            hi = mid
        if hi - lo < tol * hi:
            break
    return 0.5 * (lo + hi)


def dp_face(n_target, N, p, d, mu_face):
    """forward DP over positions for paths restricted to the face (len(n_target) colours);
    transition p (stay) and r=(1-p)/(d-1) (switch). Returns P(n_target) (float)."""
    k = len(n_target)
    r = (1 - p) / (d - 1)
    cur = {}
    for c in range(k):
        if mu_face[c]:
            key = tuple(1 if i == c else 0 for i in range(k)) + (c,)
            cur[key] = mu_face[c]
    for _ in range(N - 1):
        nxt = {}
        for key, val in cur.items():
            cnt = key[:k]
            last = key[k]
            for c in range(k):
                if cnt[c] + 1 > n_target[c]:
                    continue
                nc = list(cnt)
                nc[c] += 1
                nk = tuple(nc) + (c,)
                nxt[nk] = nxt.get(nk, 0.0) + val * (p if c == last else r)
        cur = nxt
    return sum(val for key, val in cur.items() if key[:k] == tuple(n_target))


def T3():
    say("=" * 90)
    say("T3  crossings with a general start, d=4, mu=(2/5,3/10,1/5,1/10)")
    say("-" * 90)
    d = 4
    cases = [("A: F={1,2,3} (k=3) vs vertex 1", 3, [0.4, 0.3, 0.2], 0.4, 4 / 3,
              a_const(3) + 0.5 * math.log(4 / 3), [3, 30, 300, 3000, 30000]),
             ("B: F={2,3} (k=2) vs vertex 4", 2, [0.3, 0.2], 0.1, 0.4,
              a_const(2) + math.log(0.4), [2, 20, 200, 2000, 20000])]
    for name, k, muF, mui, target, amu, Ns in cases:
        say(f"{name}: a_k(mu)={amu:+.10f}, identity target S_n = {target:.10f}")
        prev_u = None
        for N in Ns:
            t0 = time.time()
            n = [N // k] * k
            L = math.log(N)
            zg = max(1.0, L - 0.5 * math.log(max(L, 1.0001)) + amu)
            mmax = min(N, int(30 + 5 * zg))
            R1 = m1_coeffs(n, N, muF, mmax)
            C2 = m2_coeffs(n, N, muF, mmax)
            Cun = m2_coeffs(n, N, [1.0] * k, mmax)
            f1 = lambda u: m1_logratio(R1, k, N, u) - math.log(mui)
            f2 = lambda u: m2_logratio(C2, k, N, u) - math.log(mui)
            fu = lambda u: m2_logratio(Cun, k, N, u) - math.log(target)
            blo, bhi = (1e-9, 0.99) if N <= 60 else (0.3 * zg / N, 2.0 * zg / N)
            u1 = bisect_root(f1, blo, bhi)
            u2 = bisect_root(f2, blo, bhi)
            u3 = bisect_root(fu, blo, bhi)
            # truncation check
            R1b = m1_coeffs(n, N, muF, mmax + 15)
            trunc = abs(m1_logratio(R1b, k, N, u1) - m1_logratio(R1, k, N, u1))
            extra = ""
            if N <= 30:
                p1 = 1 / (1 + (d - 1) * u1)
                pb = dp_face(n, N, p1, d, muF)
                extra = f"  DP(M3) ratio at root = {pb / (mui * p1 ** (N - 1)):.14f}"
            z = N * u1
            ahat = z + 0.5 * math.log(z) - L - 1 / (8 * z)
            mono = "" if prev_u is None else f"  u decreasing: {u1 < prev_u}"
            prev_u = u1
            say(f"   N={N:>6}: z(M1)={z:.12f} z(M2)={N*u2:.12f} z(S_n=target)={N*u3:.12f}"
                f"  rel M1-M2={abs(u1/u2-1):.1e} M1-id={abs(u1/u3-1):.1e} trunc={trunc:.1e}"
                f"{extra}{mono}")
            if N > k:
                tol = 1 / z ** 2 + z ** 2 / N
                say(f"            ahat={ahat:+.6f}  ahat-a(mu)={ahat-amu:+.6f}  tol={tol:.5f}"
                    f"  within: {abs(ahat-amu) <= tol}  heuristic ((k-1)/2)z^2/N={(k-1)/2*z*z/N:.5f}"
                    f"  [{time.time()-t0:.1f}s]")


# ----------------------------------------------------------------------------------------
# T4: K_3 window with mu = (1/2,1/2,0)
# ----------------------------------------------------------------------------------------
def T4(Ns=(90, 1002, 10002, 100002, 1000002), preds=None, noshift_w=None, tolf=None,
       title="T4  K_3, mu=(1/2,1/2,0): edge window at finite N", dp=True):
    say("=" * 90)
    say(title)
    say("-" * 90)
    a2 = a_const(2)
    tef = math.log(1.5) + 2 * a_const(3) - a2
    if preds is None:
        preds = {90: (-0.298226, -0.286088, 0.012138), 1002: (-0.340235, -0.323179, 0.017057),
                 10002: (-0.363991, -0.344597, 0.019393), 100002: (-0.379849, -0.359060, 0.020789),
                 1000002: (-0.391213, -0.369503, 0.021710)}
        noshift_w = {10002: 0.024431, 100002: 0.024778, 1000002: 0.025005}
        tolf = lambda z, N: 0.5 / z ** 2 + z ** 2 / N
    mu3 = [0.5, 0.5, 0.0]
    for N in Ns:
        t0 = time.time()
        L = math.log(N)
        zg = L - 0.5 * math.log(L) + a2
        mmax = min(N, int(30 + 5 * zg))
        tcoord = lambda u: N * u - L + 0.5 * math.log(L)
        # edge (N/2, N/2, 0)
        ne = [N // 2, N // 2]
        Re = m1_coeffs(ne, N, [0.5, 0.5], mmax)
        Ce = m2_coeffs(ne, N, [1.0, 1.0], mmax)  # start-free binary center polynomial
        ledge = lambda u: m1_logratio(Re, 2, N, u)
        f_low1 = lambda u: ledge(u) - math.log(0.5)
        f_low2 = lambda u: m2_logratio(Ce, 2, N, u)  # S_{(N/2,N/2)}(u) = 1
        ulow1 = bisect_root(f_low1, 0.3 * zg / N, 2.0 * zg / N)
        ulow2 = bisect_root(f_low2, 0.3 * zg / N, 2.0 * zg / N)
        # full face max
        cache = {}

        def full_val(n3, u):
            n12 = N - n3
            n1, n2 = (n12 + 1) // 2, n12 // 2
            key = (n1, n2, n3)
            if key not in cache:
                cache[key] = m1_coeffs([n1, n2, n3], N, mu3, mmax)
            return m1_logratio(cache[key], 3, N, u)

        def full_max(u, s0):
            s = s0
            step = max(1, N // 64)
            val = full_val(s, u)
            while step >= 1:
                moved = True
                while moved:
                    moved = False
                    for cand in (s - step, s + step):
                        if 1 <= cand <= N - 2:
                            vc = full_val(cand, u)
                            if vc > val:
                                s, val, moved = cand, vc, True
                                break
                step //= 2
            return s, val

        state = {"s": int(N * (1 / 3 - 1 / (9 * zg)))}

        def f_up(u):
            s, val = full_max(u, state["s"])
            state["s"] = s
            return val - ledge(u)

        # bracket around the predicted upper end
        tup_pred = preds[N][1]
        zlo = tup_pred - 0.25 + L - 0.5 * math.log(L)
        zhi = tup_pred + 0.25 + L - 0.5 * math.log(L)
        uup = bisect_root(f_up, zlo / N, zhi / N, it=60, tol=1e-13)
        s_hat, _ = full_max(uup, state["s"])
        # 2D neighbourhood check of the maximiser (M1)
        best = None
        for dn3 in range(-2, 3):
            n3 = s_hat + dn3
            for dd in range(-3, 4):
                n12 = N - n3
                if (n12 + dd) % 2:
                    continue
                n1 = (n12 + dd) // 2
                n2 = n12 - n1
                if min(n1, n2, n3) < 1:
                    continue
                val = m1_logratio(m1_coeffs([n1, n2, n3], N, mu3, mmax), 3, N, uup)
                if best is None or val > best[0]:
                    best = (val, n1, n2, n3)
        # M2 confirmation at the bracket around uup
        nmax = [best[1], best[2], best[3]]
        C2max = m2_coeffs(nmax, N, mu3, min(N, int(20 + 3 * zg)))
        up_lo, up_hi = uup * (1 - 1e-9), uup * (1 + 1e-9)
        g_lo = m2_logratio(C2max, 3, N, up_lo) - m2_logratio(Ce, 2, N, up_lo) - math.log(0.5)
        g_hi = m2_logratio(C2max, 3, N, up_hi) - m2_logratio(Ce, 2, N, up_hi) - math.log(0.5)
        m1_m2 = abs(m1_logratio(m1_coeffs(nmax, N, mu3, mmax), 3, N, uup)
                    - m2_logratio(C2max, 3, N, uup))
        # balanced full bin and value ratio
        nb = [N // 3] * 3
        lbal = m1_logratio(m1_coeffs(nb, N, mu3, mmax), 3, N, uup)
        zup = N * uup
        tl1, tl2, tu = tcoord(ulow1), tcoord(ulow2), tcoord(uup)
        width = tu - tl1
        pl, pu, pw = preds[N]
        zl = N * ulow1
        tol_l = tolf(zl, N)
        tol_u = tolf(zup, N)
        say(f"N={N}: t_low(M1)={tl1:+.8f} t_low(A's S_N=1, M2)={tl2:+.8f} rel u diff={abs(ulow1/ulow2-1):.1e}")
        say(f"        t_up={tu:+.8f}  width={width:.6f}   predicted t_low={pl:+.6f} t_up={pu:+.6f}"
            f" width={pw:.6f}")
        say(f"        t_low-pred={tl1-pl:+.6f} (tol {tol_l:.4f}, ok {abs(tl1-pl)<=tol_l})"
            f"  t_up-pred={tu-pu:+.6f} (tol {tol_u:.4f}, ok {abs(tu-pu)<=tol_u})")
        if N in noshift_w:
            say(f"        |width-shifted pred|={abs(width-pw):.6f}  |width-noshift pred|="
                f"{abs(width-noshift_w[N]):.6f}  shifted closer: {abs(width-pw) < abs(width-noshift_w[N])}")
        say(f"        full-face maximiser at t_up: n=({best[1]},{best[2]},{best[3]})"
            f"  |n1-n2|={abs(best[1]-best[2])}  z(1/3-n3/N)={zup*(1/3-best[3]/N):.5f}"
            f" (pred n3~{N*(1/3-1/(9*zup)):.1f})")
        say(f"        z*log(M_full/P(N/3,N/3,N/3))={zup*(best[0]-lbal):.5f} (limit 1/24=0.04167)")
        say(f"        M2 confirms sign change at t_up +- 1e-9 rel: {g_lo < 0 < g_hi}"
            f"  |M1-M2| log value at maximiser={m1_m2:.1e}  [{time.time()-t0:.1f}s]")
    if not dp:
        return
    # N = 90 brute-force DP over all bins
    say("N=90 brute-force DP over all bins (M3):")
    N = 90
    L = math.log(N)

    def dp_all(u):
        d = 3
        p = 1 / (1 + (d - 1) * u)
        r = (1 - p) / (d - 1)
        cur = {}
        for c in range(3):
            if mu3[c]:
                key = (int(c == 0), int(c == 1), c)
                cur[key] = mu3[c]
        for step in range(N - 1):
            nxt = {}
            for (n1, n2, last), val in cur.items():
                for c in range(3):
                    nk = (n1 + (c == 0), n2 + (c == 1), c)
                    nxt[nk] = nxt.get(nk, 0.0) + val * (p if c == last else r)
            cur = nxt
        P = {}
        for (n1, n2, last), val in cur.items():
            key = (n1, n2, N - n1 - n2)
            P[key] = P.get(key, 0.0) + val
        return P, p

    def modes(u):
        P, p = dp_all(u)
        mx = max(P.values())
        return sorted(n for n, v in P.items() if v >= mx * (1 - 1e-12)), P, p

    # compare DP with M1 on a few bins
    u_test = (L - 0.5 * math.log(L) - 0.3) / N
    P, p = dp_all(u_test)
    worst = 0.0
    for n in [(45, 45, 0), (30, 30, 30), (31, 32, 27), (80, 5, 5), (1, 1, 88), (90, 0, 0)]:
        supp = [i for i in range(3) if n[i] > 0]
        nn = [n[i] for i in supp]
        muu = [mu3[i] for i in supp]
        val = math.exp(m1_logratio(m1_coeffs(nn, N, muu, 90), len(nn), N, u_test)) \
            if len(nn) > 1 else muu[0]
        worst = max(worst, abs(val * p ** (N - 1) / P[n] - 1))
    say(f"   DP vs M1 on 6 bins at t=-0.3: worst rel diff {worst:.1e};"
        f" total mass {sum(P.values()):.15f}")
    seq = []
    for i in range(0, 71):
        t = -1.0 + 0.02 * i
        u = (L - 0.5 * math.log(L) + t) / N
        ms, _, _ = modes(u)
        lab = ["".join(str(int(x > 0)) for x in m) for m in ms]
        desc = f"{ms}"
        if not seq or seq[-1][1] != desc:
            seq.append((round(t, 2), desc))
    for t, desc in seq:
        say(f"   from t={t:+.2f}: global modes {desc}")


def main():
    t0 = time.time()
    T1()
    T2()
    T3()
    T4()
    T4(Ns=(3000, 30000, 300000),
       preds={3000: (-0.346109, -0.314003, 0.032106), 30000: (-0.371064, -0.348481, 0.022582),
              300000: (-0.385511, -0.363855, 0.021656)},
       noshift_w={3000: 0.037953, 30000: 0.027062, 300000: 0.025283},
       tolf=lambda z, N: 0.2 / z ** 2 + 3 * z / N,
       title="T4' (registered after T4 was killed): same model, discrete z^2/N terms included",
       dp=False)
    say(f"total time {time.time()-t0:.1f}s")
    with open("data/general_start_output.txt", "w", encoding="utf-8") as fh:
        fh.write("\n".join(OUT) + "\n")


if __name__ == "__main__":
    main()
