"""Checks for Proposition 4.15 and Lemma A.3 (the tree formula for K_F on every face).

Tests of the forest formula
   det Sigma_alpha = (prod alpha)^2 tree(f + f^T) / arb(f)^2,   f_ij = l_i q_ij r_j,
and of the resulting formula for C_F(alpha) and K_F.
Trees and arborescences are ENUMERATED (no determinants), so the test does not
depend on the matrix-tree theorem.  Run: python -B verify_forest.py   (a few minutes)
"""
import itertools, math, sys, random
from fractions import Fraction
import numpy as np, mpmath as mp, sympy as sp
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import verify_second_order as V   # the script of the paper (its main is guarded)


def arb(f, root):
    """Sum over spanning trees oriented toward root of prod f[a][parent(a)] (enumeration)."""
    k = len(f)
    others = [a for a in range(k) if a != root]
    tot = 0
    for par in itertools.product(range(k), repeat=k - 1):
        p = dict(zip(others, par))
        ok = True
        for a in others:
            if p[a] == a:
                ok = False
                break
            x, steps = a, 0
            while x != root and steps <= k:
                x = p[x]
                steps += 1
            if x != root:
                ok = False
                break
        if ok:
            w = 1
            for a in others:
                w = w * f[a][p[a]]
            tot = tot + w
    return tot


def tree(c):
    """Sum over spanning trees of prod c (c symmetric). Each tree has one orientation toward 0."""
    return arb(c, 0)


# ---------- A. exact rational test of the core identity for arbitrary irreducible generators
def test_exact(k, rng, sparse=False):
    G = [[0] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            if i != j and (not sparse or (j == (i + 1) % k) or rng.random() < 0.4):
                G[i][j] = Fraction(rng.randint(1, 9), rng.randint(1, 9))
        G[i][i] = -sum(G[i])
    w = [arb(G, i) for i in range(k)]
    W = sum(w)
    pi = [x / W for x in w]                       # Markov chain tree theorem
    Gs = sp.Matrix(G)
    pis = sp.Matrix(pi)
    assert (pis.T * Gs) == sp.zeros(1, k)
    one = sp.ones(k, 1)
    Z = (one * pis.T - Gs).inv() - one * pis.T
    D = sp.diag(*pi)
    Gam = D * Z + Z.T * D
    detS = Gam[1:, 1:].det()
    f = [[pi[i] * G[i][j] if i != j else 0 for j in range(k)] for i in range(k)]
    fs = [[f[i][j] + f[j][i] for j in range(k)] for i in range(k)]
    arbs = [arb(f, i) for i in range(k)]
    assert len(set(arbs)) == 1, "arb(f) depends on the root"
    P = math.prod(pi)
    rhs1 = tree(fs) / W ** 2
    rhs2 = P ** 2 * tree(fs) / arbs[0] ** 2
    assert detS == rhs1 == rhs2, (k, detS, rhs1, rhs2)
    assert W == arbs[0] / P
    assert (one * pis.T - Gs).det() == W
    assert Gam.adjugate() == detS * sp.ones(k, k)
    # the factorization Gamma = Z^T S Z
    S = -(D * Gs + Gs.T * D)
    assert Z.T * S * Z == Gam
    return True


rng = random.Random(1)
n = 0
for k in (2, 3, 4, 5, 6):
    for t in range({2: 20, 3: 40, 4: 40, 5: 15, 6: 4}[k]):
        test_exact(k, rng, sparse=(t % 2 == 1))
        n += 1
print(f"A. exact rational identity det Sigma = tree(f+f^T)/W^2 = (prod pi)^2 tree(f+f^T)/arb(f)^2: "
      f"{n} generators, k=2..6, all EXACT", flush=True)

# ---------- B. symbolic: general 3-state generator, and directed 3-cycle with rates a,b,c
q12, q13, q21, q23, q31, q32 = sp.symbols('q12 q13 q21 q23 q31 q32', positive=True)


def sym_check(G):
    k = G.shape[0]
    Gl = [[G[i, j] for j in range(k)] for i in range(k)]
    w = [arb(Gl, i) for i in range(k)]
    W = sum(w)
    pi = [sp.together(x / W) for x in w]
    one = sp.ones(k, 1)
    pis = sp.Matrix(pi)
    M = (one * pis.T - G).applyfunc(sp.cancel)
    Z = (M.adjugate() / sp.cancel(M.det())).applyfunc(sp.cancel) - one * pis.T
    Gam = (sp.diag(*pi) * Z + Z.T * sp.diag(*pi)).applyfunc(sp.cancel)
    detS = sp.cancel(Gam[1:, 1:].det())
    f = [[pi[i] * Gl[i][j] if i != j else 0 for j in range(k)] for i in range(k)]
    fs = [[f[i][j] + f[j][i] for j in range(k)] for i in range(k)]
    rhs = sp.cancel(tree(fs) / W ** 2)
    return sp.cancel(detS - rhs), sp.factor(rhs)


G3 = sp.Matrix([[-(q12 + q13), q12, q13], [q21, -(q21 + q23), q23], [q31, q32, -(q31 + q32)]])
d, _ = sym_check(G3)
print("B1. general 3-state generator, symbolic difference:", d, flush=True)
a, b, c = sp.symbols('a b c', positive=True)
Gc = sp.Matrix([[-a, a, 0], [0, -b, b], [c, 0, -c]])
d, val = sym_check(Gc)
print("B2. directed 3-cycle with rates a,b,c: difference", d, "; det Sigma =", val)
val_paper = val.subs({a: b, b: 1, c: 1}, simultaneous=True)
print("    at rates (b,1,1): det Sigma =", sp.factor(val_paper), "; equals 3b^2/(1+2b)^4:",
      sp.simplify(val_paper - 3 * b ** 2 / (1 + 2 * b) ** 4) == 0, flush=True)


# ---------- C. full pipeline in floats against consts_A of the paper (K_F and C_F(alpha))
def formula(A, q, mu, alpha=None):
    A = np.asarray(A, float)
    q = np.asarray(q, float)
    mu = np.asarray(mu, float)
    k = len(q)
    if alpha is None:
        s, r, l = V.perron(A - np.diag(q))
        l = l / (l @ r)
        al = l * r
        theta = q + s
    else:
        al = np.asarray(alpha, float)
        theta, r = V.tilt_radii(A, al)
        l = al / r
    f = l[:, None] * A * r[None, :]
    np.fill_diagonal(f, 0)
    fl = f.tolist()
    fs = (f + f.T).tolist()
    ar = arb(fl, 0)
    tr = tree(fs)
    P = float(np.prod(al))
    detS = P ** 2 * tr / ar ** 2
    C = float(mu @ r) * float(l.sum()) * (2 * math.pi) ** (-(k - 1) / 2) * ar / (P * math.sqrt(tr))
    ev = np.linalg.eigvals(np.diag(theta) - A)
    ev = ev[np.argsort(np.abs(ev))][1:]
    return detS, C, ar / P, np.prod(ev).real


def run_float(A, q, mu, alpha=None):
    ref = V.consts_A(A, q, mu, alpha)
    detS, C, w1, w2 = formula(A, q, mu, alpha)
    return max(abs(detS / ref['detS'] - 1), abs(C / ref['K'] - 1), abs(w1 / w2 - 1))


rs = np.random.RandomState(5)
worst = 0
cnt = 0
for k in (3, 4, 5):
    for t in range(60 if k < 5 else 20):
        A = rs.uniform(0.2, 3.0, (k, k))
        np.fill_diagonal(A, 0)
        if t % 3 == 1:   # sparse: a cycle plus a few chords
            M = np.zeros((k, k))
            for i in range(k):
                M[i, (i + 1) % k] = 1
            M = np.maximum(M, rs.rand(k, k) < 0.3)
            np.fill_diagonal(M, 0)
            A = A * M
        q = A.sum(1) + rs.uniform(0.0, 2.0, k)       # extra exit rates out of the face
        mu = rs.dirichlet(np.ones(k))
        worst = max(worst, run_float(A, q, mu))
        cnt += 1
        al = rs.dirichlet(3 * np.ones(k))
        worst = max(worst, run_float(A, q, mu, al))
        cnt += 1
print(f"C. K_F and C_F(alpha) against consts_A on {cnt} random non-reversible cases "
      f"(k=3,4,5, complete and sparse): max rel. error {worst:.2e}", flush=True)

worst = 0
for k in (3, 4):
    for t in range(30):
        S = rs.uniform(0.2, 2, (k, k))
        S = S + S.T
        np.fill_diagonal(S, 0)
        nu = rs.uniform(0.5, 2, k)
        A = S / nu[:, None]         # nu_i q_ij = nu_j q_ji
        q = A.sum(1) + rs.uniform(0, 1, k)
        mu = rs.dirichlet(np.ones(k))
        al = rs.dirichlet(3 * np.ones(k))
        detS, C, _, _ = formula(A, q, mu, al)
        cij = np.sqrt(np.outer(al, al)) * A * np.sqrt(np.outer(nu, 1 / nu))
        b_det = 2 ** (k - 1) * np.prod(al) ** 2 / tree(cij.tolist())
        worst = max(worst, abs(detS / b_det - 1))
print(f"D. reversible faces: new formula against Prop. constant(b), max rel. error {worst:.2e}", flush=True)

for bb in (2.5, 3.0, 7.0):
    A = np.array([[0, bb, 0], [0, 0, 1], [1, 0, 0.]])
    q = np.array([bb, 1, 1.])
    mu = np.array([1, 0, 0.])
    detS, C, _, _ = formula(A, q, mu)
    Kp = (1 + 2 * bb) ** 2 / (2 * math.sqrt(3) * math.pi * bb)
    print(f"E. 3-cycle b={bb}: K formula {C:.15f}  Prop. threecycle {Kp:.15f}  rel.diff {abs(C / Kp - 1):.1e}")

# ---------- F. 50-digit check with det Sigma obtained independently as det Hess(Lambda_0)(0),
# by numerical differentiation of the Perron root of Q_F + diag(0, beta)
mp.mp.dps = 50


def mp_perron(M):
    E, ER = mp.eig(M)
    i = max(range(len(E)), key=lambda j: mp.re(E[j]))
    return mp.re(E[i])


def mp_case(k, seed):
    r_ = random.Random(seed)
    A = mp.matrix(k, k)
    for i in range(k):
        for j in range(k):
            if i != j:
                A[i, j] = mp.mpf(r_.randint(1, 30)) / 10
    q = [sum(A[i, j] for j in range(k)) + mp.mpf(r_.randint(0, 20)) / 10 for i in range(k)]
    QF = A - mp.diag(q)
    Lam = lambda *beta: mp_perron(QF + mp.diag([0] + list(beta)))
    H = mp.matrix(k - 1, k - 1)
    for i in range(k - 1):
        for j in range(i, k - 1):
            nn = [0] * (k - 1)
            nn[i] += 1
            nn[j] += 1
            H[i, j] = H[j, i] = mp.diff(Lam, [0] * (k - 1), nn)
    detS_num = mp.det(H)
    E, ER = mp.eig(QF)
    E2, EL = mp.eig(QF.T)
    i = max(range(k), key=lambda j: mp.re(E[j]))
    i2 = max(range(k), key=lambda j: mp.re(E2[j]))
    r = [abs(mp.re(ER[a, i])) for a in range(k)]
    l = [abs(mp.re(EL[a, i2])) for a in range(k)]
    s = sum(x * y for x, y in zip(l, r))
    l = [x / s for x in l]
    f = [[l[a] * A[a, b] * r[b] if a != b else mp.mpf(0) for b in range(k)] for a in range(k)]
    fs = [[f[a][b] + f[b][a] for b in range(k)] for a in range(k)]
    P = mp.fprod(l[a] * r[a] for a in range(k))
    detS_f = P ** 2 * tree(fs) / arb(f, 0) ** 2
    lamF = -mp.re(E[i])
    gap = mp.fprod(-E[j] - lamF for j in range(k) if j != i)
    return abs(detS_num / detS_f - 1), abs(mp.re(gap) / (arb(f, 0) / P) - 1)


for k, seed in ((3, 1), (3, 2), (4, 3), (4, 4)):
    e1, e2 = mp_case(k, seed)
    print(f"F. k={k} seed={seed}: |det Hess(Lambda_0)/formula - 1| = {mp.nstr(e1, 3)},  "
          f"|gap product/(arb/prod alpha) - 1| = {mp.nstr(e2, 3)}", flush=True)
