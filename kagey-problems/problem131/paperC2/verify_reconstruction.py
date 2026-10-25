"""Checks of Sections `sec:minors`, `sec:modal` and `sec:reversible` of Paper C2.

  1. Symbolic identities (sympy). The pair-entry time t_ij of Theorem
     `thm:reversible-reconstruction` is the tie 1 + tau lambda_ij(v) = tau (q_i - xi_bar) of the pair with
     its singleton, and w_ij = s_ij/t_ij + 1/t_ij^2 with s_ij = xi_bar - x_i + x_j inverts it. On three states,
     det(-Q) = q1 q2 q3 - q1 w23 - q2 w13 - q3 w12 - c - c', c + c' and c c' in terms of the minors,
     the 2x2 principal minors q_i q_j - w_ij, and the time reversal Q* has the exit rates and the
     products of Q and the oriented product c' (Remark `rem:three-states`). The family Q_ell of
     Remark `rem:partial-data` has zero row sums, detailed balance with nu = (1, 4/ell^2, 1),
     w12 = w23 = 1 and w13 = (ell - 2/ell)^2.
  2. The reversible design on 40 random reversible chains with 4 states on random connected graphs,
     with the bounds R and b of the design taken up to 30 percent loose. Lemma `lem:suppression`:
     on a grid of 13 x 13 points (xi, tau) for every ordered pair, every face that leaves {i,j}
     scores at least 3/4 above the best face inside {i,j}. The singleton boundaries, found by
     bisection on the strict winner, give q_i - q_1; the pair boundaries give t_ij; and the
     reconstruction of part (c) returns Q and pi.
  3. Theorem `thm:stability`. The product error |w_hat - w| <= (88/9) eps on 200000 random cells and
     at the extreme corner; phi_min >= phi_* and lambda_2(S) >= g_* on 2000 random reversible chains
     with 2 to 6 states; and on a fixed chain with 4 states the reconstruction from coordinates
     perturbed by at most eps is a reversible generator on the graph E with ||Q_hat - Q||/(R eps) bounded
     as eps runs from 1e-2 to 1e-5.
  4. Cut-transposes (Theorem `thm:nonreversible`(c)). On random irreducible generators with 4 to 6
     states and rank-one blocks across a cut, the cut-transpose of -Q has the principal minors of
     -Q, is irreducible, and its generator point (the normalization (N)) is a generator with the
     same minors; we count how often it is neither Q nor Q*. The example with 4 states printed
     after the proof is checked in exact rational arithmetic.
  5. The gradient of the Perron branch: d lambda_F / d v_i = -(l o r)_i and
     det(I - 1 beta'^T) = beta_1 (proof of Lemma `lem:perron-branch`), by central differences.
  6. Fibers on three states (Theorem `thm:nonreversible`(d)): for 200 random generators with all
     rates positive, every generator with the same principal minors, found by a scan and root
     bracketing of the one remaining equation, is Q or Q*, and both occur; and for the irreducible
     generators among 30 random ones with some zero rates, every irreducible solution that a
     least-squares search finds from Q, from Q* and from a 7 x 7 x 7 grid of starts is Q or Q*.

Needs numpy, scipy and sympy. Run:  py -I verify_reconstruction.py   (about a minute)
"""
import itertools
from collections import Counter
from fractions import Fraction

import numpy as np
import scipy.optimize as so
import sympy as sp
from scipy.optimize import brentq

CHECKS = 0


def ok(cond, what):
    global CHECKS
    if not cond:
        raise AssertionError(what)
    CHECKS += 1
    print("  ok   ", what, flush=True)


def part1():
    print("1. Symbolic identities")
    qi, qj, H, w = sp.symbols('q_i q_j H w', positive=True)
    a, c = qi - H, qj
    lam_pair = ((a + c) - sp.sqrt((c - a) ** 2 + 4 * w)) / 2
    ok(sp.simplify((a - lam_pair) * (c - lam_pair) - w) == 0,
       "lambda_ij(v) is the smaller eigenvalue of [[q_i - H, -sqrt w], [-sqrt w, q_j]]")
    s = H - (qi - qj)
    t = (sp.sqrt(s ** 2 + 4 * w) + s) / (2 * w)
    ok(sp.simplify(1 + t * lam_pair - t * (qi - H)) == 0, "the pair and the singleton tie at tau = t_ij")
    ok(sp.simplify(s / t + 1 / t ** 2 - w) == 0, "w_ij = s_ij/t_ij + 1/t_ij^2 with s_ij = xi_bar - x_i + x_j")
    q12, q13, q21, q23, q31, q32 = sp.symbols('q12 q13 q21 q23 q31 q32', positive=True)
    Q = sp.Matrix([[-(q12 + q13), q12, q13], [q21, -(q21 + q23), q23], [q31, q32, -(q31 + q32)]])
    q1, q2, q3 = -Q[0, 0], -Q[1, 1], -Q[2, 2]
    w12, w23, w13 = q12 * q21, q23 * q32, q13 * q31
    cc, cp = q12 * q23 * q31, q13 * q32 * q21
    ok(sp.expand((-Q).det()) == 0, "det(-Q) = 0 for a generator on three states")
    ok(sp.expand(cc + cp - (q1 * q2 * q3 - q1 * w23 - q2 * w13 - q3 * w12)) == 0,
       "c + c' = q1 q2 q3 - q1 w23 - q2 w13 - q3 w12")
    ok(sp.expand(cc * cp - w12 * w23 * w13) == 0, "c c' = w12 w23 w13")
    ok(all(sp.expand((-Q).extract([i, j], [i, j]).det() - ((-Q)[i, i] * (-Q)[j, j] - ww)) == 0
           for (i, j, ww) in [(0, 1, w12), (1, 2, w23), (0, 2, w13)]),
       "the 2x2 principal minors are q_i q_j - w_ij")
    pi = Q.T.nullspace()[0]
    pi = sp.simplify(pi / sum(pi))
    Dp = sp.diag(*pi)
    Qs = sp.simplify(Dp.inv() * Q.T * Dp)
    ok(all(sp.simplify(e) == 0 for e in Qs * sp.ones(3, 1))
       and sp.simplify(Qs[0, 1] * Qs[1, 2] * Qs[2, 0] - cp) == 0
       and all(sp.simplify(Qs[i, i] - Q[i, i]) == 0 for i in range(3))
       and sp.simplify(Qs[0, 1] * Qs[1, 0] - w12) == 0,
       "Q* is a generator with the exit rates and products of Q and the oriented product c'")
    l = sp.symbols('ell', positive=True)
    z = l - 2 / l
    Ql = sp.Matrix([[-l, 2 / l, z], [l / 2, -l, l / 2], [z, 2 / l, -l]])
    pil = sp.Matrix([1, 4 / l ** 2, 1])
    ok(all(sp.simplify(e) == 0 for e in Ql * sp.ones(3, 1))
       and all(sp.simplify(pil[i] * Ql[i, j] - pil[j] * Ql[j, i]) == 0 for i in range(3) for j in range(3))
       and sp.simplify(Ql[0, 1] * Ql[1, 0]) == 1 and sp.simplify(Ql[1, 2] * Ql[2, 1]) == 1
       and sp.simplify(Ql[0, 2] * Ql[2, 0] - z ** 2) == 0,
       "Q_ell: zero row sums, detailed balance with (1, 4/ell^2, 1), w12 = w23 = 1, w13 = z^2")


def connected(F, adj):
    F = list(F)
    seen = {F[0]}
    st = [F[0]]
    while st:
        x = st.pop()
        for y in F:
            if y not in seen and adj[x, y]:
                seen.add(y)
                st.append(y)
    return len(seen) == len(F)


def part2():
    print("2. The reversible design on random chains with 4 states")
    rng = np.random.default_rng(20261024)
    worst_gap, nfail = np.inf, 0
    errs_d, errs_t, errs_q, errs_pi = [], [], [], []
    for trial in range(40):
        d = 4
        alle = [(0, 1), (1, 2), (2, 3), (0, 2), (0, 3), (1, 3)]
        while True:
            E = [e for e in alle if rng.random() < 0.6]
            adj = np.zeros((d, d), bool)
            for i, j in E:
                adj[i, j] = adj[j, i] = True
            if E and connected(range(d), adj):
                break
        pi = rng.uniform(0.3, 1.0, d)
        pi /= pi.sum()
        Q = np.zeros((d, d))
        for (i, j) in E:
            cnd = rng.uniform(0.3, 2.0)
            Q[i, j] = cnd / pi[i]
            Q[j, i] = cnd / pi[j]
        Q -= np.diag(Q.sum(1))
        sq = np.sqrt(pi)
        S = np.diag(sq) @ (-Q) @ np.diag(1 / sq)
        S = (S + S.T) / 2
        R = np.linalg.norm(S, 2) * (1 + rng.uniform(0, 0.3))
        b = min(np.sqrt(Q[i, j] * Q[j, i]) for i, j in E) * (1 - rng.uniform(0, 0.3))
        H = 2 * R
        tau0 = 1 / (2 * R)
        U = 8 * R / b ** 2
        M = 4 * R + 4 * U * R ** 2
        faces = [F for k in range(1, d + 1) for F in itertools.combinations(range(d), k) if connected(F, adj)]

        def lam(F, v):
            F = list(F)
            return np.linalg.eigvalsh(S[np.ix_(F, F)] - np.diag(v[F]))[0]

        def score(F, v, tau):
            return len(F) - 1 + tau * lam(F, v)

        for (i, j) in itertools.permutations(range(d), 2):
            for delta in np.linspace(-3 * R, 3 * R, 13):
                for tau in np.geomspace(1 / (4 * R), U, 13):
                    v = np.full(d, -M)
                    v[i] = delta
                    v[j] = 0
                    inside = [F for F in faces if set(F) <= {i, j}]
                    best_in = min(score(F, v, tau) for F in inside)
                    out = [score(F, v, tau) for F in faces if not set(F) <= {i, j}]
                    if out:
                        g = min(out) - best_in
                        worst_gap = min(worst_gap, g)
                        nfail += g < 0.75 - 1e-12

        def winner_field(v, tau):
            sc = {F: score(F, v, tau) for F in faces}
            return min(sc, key=sc.get)

        d_est = np.zeros(d)
        for i in range(1, d):
            lo, hi = -3 * R, 3 * R
            fld = lambda delta: np.array([0 if k == 0 else (delta if k == i else -M) for k in range(d)])
            assert winner_field(fld(lo), tau0) == (0,) and winner_field(fld(hi), tau0) == (i,)
            for _ in range(80):
                mid = (lo + hi) / 2
                if winner_field(fld(mid), tau0) == (0,):
                    lo = mid
                else:
                    hi = mid
            d_est[i] = (lo + hi) / 2
        q = -np.diag(Q)
        errs_d.append(np.max(np.abs(d_est - (q - q[0]))))
        W, terr = {}, 0.0
        for (i, j) in E:
            Dl = d_est[i] - d_est[j]
            ww = Q[i, j] * Q[j, i]
            t_formula = (np.sqrt((H - Dl) ** 2 + 4 * ww) + H - Dl) / (2 * ww)
            assert 1 / R - 1e-12 <= t_formula < U / 2
            fld = np.array([H if k == i else (0 if k == j else -M) for k in range(d)])
            lo, hi = 1 / (4 * R), U
            assert winner_field(fld, lo) == (i,) and set(winner_field(fld, hi)) == {i, j}
            for _ in range(80):
                mid = (lo + hi) / 2
                if winner_field(fld, mid) == (i,):
                    lo = mid
                else:
                    hi = mid
            t = (lo + hi) / 2
            terr = max(terr, abs(t - t_formula))
            W[(i, j)] = (H - Dl) / t + 1 / t ** 2
        errs_t.append(terr)
        B = np.diag(d_est)
        for (i, j), ww in W.items():
            B[i, j] = B[j, i] = -np.sqrt(ww)
        ev, Vv = np.linalg.eigh(B)
        h = np.abs(Vv[:, 0])
        Qh = -np.diag(1 / h) @ (B - ev[0] * np.eye(d)) @ np.diag(h)
        errs_q.append(np.max(np.abs(Qh - Q)))
        errs_pi.append(np.max(np.abs(h ** 2 - pi)))
    ok(nfail == 0 and worst_gap >= 0.75,
       f"Lemma lem:suppression: least gap {worst_gap:.4f} >= 3/4 over all cells of the 40 chains")
    ok(max(errs_d) < 1e-10, f"singleton boundaries give q_i - q_1 (max error {max(errs_d):.1e})")
    ok(max(errs_t) < 1e-10, f"pair boundaries give t_ij (max error {max(errs_t):.1e})")
    ok(max(errs_q) < 1e-9 and max(errs_pi) < 1e-9,
       f"the reconstruction returns Q and pi (max errors {max(errs_q):.1e}, {max(errs_pi):.1e})")


def recon(D, s, E, d):
    W = {}
    for (i, j) in E:
        W[(i, j)] = (2 - D[i] + D[j]) / s[(i, j)] + s[(i, j)] ** -2
    B = np.diag(D)
    for (i, j), w in W.items():
        B[i, j] = B[j, i] = -np.sqrt(w)
    ev, V = np.linalg.eigh(B)
    h = np.abs(V[:, 0])
    return -np.diag(1 / h) @ (B - ev[0] * np.eye(d)) @ np.diag(h)


def part3():
    print("3. Stability")
    rng = np.random.default_rng(7)
    worst = 0.0
    for _ in range(200000):
        a = rng.uniform(1, 3)
        s = 1 + rng.exponential(2)
        eps = rng.uniform(0, 0.25)
        ah = a + rng.uniform(-2 * eps, 2 * eps)
        sh = s + rng.uniform(-eps, eps)
        if eps > 0:
            worst = max(worst, abs(ah / sh + 1 / sh ** 2 - a / s - 1 / s ** 2) / eps)
    for eps in [1e-6, 0.1, 0.25]:
        a, s, ah, sh = 3, 1, 3 + 2 * eps, 1 - eps
        worst = max(worst, abs(ah / sh + 1 / sh ** 2 - a / s - 1 / s ** 2) / eps)
    ok(worst <= 88 / 9, f"product error / eps <= {worst:.4f} <= 88/9 = {88 / 9:.4f}")
    okh = okg = True
    ratio_h, ratio_g = [], []
    for _ in range(2000):
        d = rng.integers(2, 7)
        alle = list(itertools.combinations(range(d), 2))
        while True:
            E = [e for e in alle if rng.random() < 0.5]
            adj = np.zeros((d, d), bool)
            for i, j in E:
                adj[i, j] = adj[j, i] = True
            if E and connected(range(d), adj):
                break
        pi = rng.uniform(0.05, 1, d)
        pi /= pi.sum()
        Q = np.zeros((d, d))
        for i, j in E:
            c = rng.uniform(0.05, 2)
            Q[i, j] = c / pi[i]
            Q[j, i] = c / pi[j]
        Q -= np.diag(Q.sum(1))
        sq = np.sqrt(pi)
        S = np.diag(sq) @ (-Q) @ np.diag(1 / sq)
        S = (S + S.T) / 2
        R = np.linalg.norm(S, 2)
        b = min(np.sqrt(Q[i, j] * Q[j, i]) for i, j in E)
        hs = (b / R) ** (d - 1) / np.sqrt(d)
        gs = 2 * b * hs ** 2 / (d - 1)
        ev = np.linalg.eigvalsh(S)
        okh &= bool(sq.min() >= hs * (1 - 1e-12))
        okg &= bool(ev[1] >= gs * (1 - 1e-12))
        ratio_h.append(sq.min() / hs)
        ratio_g.append(ev[1] / gs)
    ok(okh and okg, f"phi_min >= phi_* and lambda_2(S) >= g_* on 2000 chains "
                    f"(least ratios {min(ratio_h):.3f}, {min(ratio_g):.3f})")
    d = 4
    E = [(0, 1), (1, 2), (2, 3), (0, 2)]
    pi = np.array([.2, .3, .25, .25])
    Q = np.zeros((d, d))
    for i, j in E:
        c = rng.uniform(0.3, 1)
        Q[i, j] = c / pi[i]
        Q[j, i] = c / pi[j]
    Q -= np.diag(Q.sum(1))
    sq = np.sqrt(pi)
    S = np.diag(sq) @ (-Q) @ np.diag(1 / sq)
    R = np.linalg.norm(S, 2)
    Qn = Q / R
    q = -np.diag(Qn)
    D = q - q[0]
    s = {}
    for (i, j) in E:
        w = Qn[i, j] * Qn[j, i]
        Dl = D[i] - D[j]
        s[(i, j)] = (np.sqrt((2 - Dl) ** 2 + 4 * w) + 2 - Dl) / (2 * w)
    ok(np.abs(recon(D, s, E, d) - Qn).max() < 1e-12, "exact coordinates reconstruct Q/R")
    ms = []
    for eps in [1e-2, 1e-3, 1e-4, 1e-5]:
        m = 0.0
        for _ in range(200):
            Dh = D + rng.uniform(-eps, eps, d)
            Dh[0] = 0
            sh = {e: s[e] + rng.uniform(-eps, eps) for e in E}
            Qh = recon(Dh, sh, E, d)
            assert np.all(Qh[~np.eye(d, dtype=bool)] >= -1e-14) and np.allclose(Qh.sum(1), 0)
            assert all((abs(Qh[i, j]) > 0) == ((i, j) in E or (j, i) in E) for i in range(d) for j in range(d) if i != j)
            m = max(m, np.linalg.norm(Qh - Qn, 2) / eps)
        ms.append(m)
    ok(max(ms) < 2 * min(ms), "perturbed reconstructions are reversible generators on the graph E, with "
                              "max ||Q_hat - Q||/(R eps) = " + ", ".join(f"{m:.2f}" for m in ms)
       + " for eps = 1e-2 .. 1e-5")


def minors(A):
    n = len(A)
    return {S: np.linalg.det(A[np.ix_(S, S)]) for k in range(1, n + 1) for S in itertools.combinations(range(n), k)}


def strongly_connected(A):
    n = len(A)
    G = (np.abs(A) > 1e-13) & ~np.eye(n, dtype=bool)
    R = np.eye(n, dtype=bool) | G
    for _ in range(n):
        R = R | ((R.astype(int) @ R.astype(int)) > 0)
    return R.all()


def normalize(C):
    ev, V = np.linalg.eig(-C)
    k = np.argmax(ev.real)
    x = np.real(V[:, k])
    x = x / x.sum()
    assert abs(ev[k]) < 1e-9 and np.all(x > 0)
    return -np.diag(1 / x) @ C @ np.diag(x)


def time_reversal(Q):
    ev, V = np.linalg.eig(Q.T)
    pi = np.real(V[:, np.argmin(abs(ev))])
    pi /= pi.sum()
    return np.diag(1 / pi) @ Q.T @ np.diag(pi)


def part4():
    print("4. Cut-transposes")
    rng = np.random.default_rng(11)
    nok = ntot = third = 0
    for trial in range(300):
        d = rng.integers(4, 7)
        k = rng.integers(2, d - 1)
        X, Y = list(range(k)), list(range(k, d))
        Q = np.zeros((d, d))
        for blk in (X, Y):
            for i in blk:
                for j in blk:
                    if i != j and rng.random() < 0.5:
                        Q[i, j] = rng.uniform(0.2, 2)
        a = rng.uniform(0.2, 1, len(X)) * (rng.random(len(X)) < 0.6)
        b = rng.uniform(0.2, 1, len(Y)) * (rng.random(len(Y)) < 0.6)
        c = rng.uniform(0.2, 1, len(Y)) * (rng.random(len(Y)) < 0.6)
        u = rng.uniform(0.2, 1, len(X)) * (rng.random(len(X)) < 0.6)
        if not (a.any() and b.any() and c.any() and u.any()):
            continue
        Q[np.ix_(X, Y)] = np.outer(a, b)
        Q[np.ix_(Y, X)] = np.outer(c, u)
        np.fill_diagonal(Q, 0)
        Q -= np.diag(Q.sum(1))
        if not strongly_connected(Q):
            continue
        A = -Q
        ntot += 1
        C = A.copy()
        C[np.ix_(X, Y)] = -np.outer(a, c)
        C[np.ix_(Y, X)] = -np.outer(b, u)
        C[np.ix_(Y, Y)] = A[np.ix_(Y, Y)].T
        mA, mC = minors(A), minors(C)
        good = max(abs(mA[S] - mC[S]) for S in mA) < 1e-9 and strongly_connected(C)
        Qp = normalize(C)
        good = good and np.allclose(Qp.sum(1), 0) and np.all(Qp[~np.eye(d, dtype=bool)] >= -1e-12)
        mQp = minors(-Qp)
        good = good and max(abs(mA[S] - mQp[S]) for S in mA) < 1e-8
        nok += good
        third += np.abs(Qp - Q).max() > 1e-6 and np.abs(Qp - time_reversal(Q)).max() > 1e-6
    ok(nok == ntot and third > 0,
       f"{nok}/{ntot} cut-transposes have the minors of -Q, are irreducible, and normalize to a "
       f"generator with the same minors; {third} of these are neither Q nor Q*")
    # the printed example, in exact arithmetic
    F_ = Fraction
    Qe = sp.Matrix([[F_(-47, 10), F_(7, 10), 1, 3], [F_(13, 10), F_(-93, 10), 2, 6],
                    [2, 2, F_(-22, 5), F_(2, 5)], [1, 1, 2, -4]])
    ok(all(sum(Qe.row(i)) == 0 for i in range(4))
       and Qe[0:2, 2:4] == sp.Matrix([1, 2]) * sp.Matrix([[1, 3]])
       and Qe[2:4, 0:2] == sp.Matrix([2, 1]) * sp.Matrix([[1, 1]]),
       "the example Q is a generator with Q[X,Y] = (1,2)^T(1,3) and Q[Y,X] = (2,1)^T(1,1)")
    A = -Qe
    a, b, c, u = sp.Matrix([1, 2]), sp.Matrix([1, 3]), sp.Matrix([2, 1]), sp.Matrix([1, 1])
    C = A.copy()
    C[0:2, 2:4] = -a * c.T
    C[2:4, 0:2] = -b * u.T
    C[2:4, 2:4] = A[2:4, 2:4].T
    x = C.nullspace()[0]
    x = x / x[0]
    assert all(e > 0 for e in x)
    Qp = -sp.diag(*x).inv() * C * sp.diag(*x)
    subsets = [S for k in range(1, 5) for S in itertools.combinations(range(4), k)]
    ok(all(A.extract(list(S), list(S)).det() == (-Qp).extract(list(S), list(S)).det() for S in subsets),
       "the generator point Q' of the cut-transpose has the fifteen principal minors of -Q")
    ok(Qp[0, 2] == sp.Rational(50, 21) and Qp[3, 0] == sp.Rational(63, 34) and Qp[3, 2] == sp.Rational(5, 17)
       and all(sum(Qp.row(i)) == 0 for i in range(4)),
       "q'_13 = 50/21, q'_41 = 63/34, q'_43 = 5/17, zero row sums")
    printed = [[-4.7, 0.7, 2.3810, 1.6190], [1.3, -9.3, 4.7619, 3.2381],
               [0.84, 0.84, -4.4, 2.72], [1.8529, 1.8529, 0.2941, -4]]
    ok(all(abs(float(Qp[i, j]) - printed[i][j]) < 5e-5 for i in range(4) for j in range(4)),
       "Q' agrees with the displayed matrix to four decimals")
    pi = Qe.T.nullspace()[0]
    pi = pi / sum(pi)
    Qs = sp.diag(*pi).inv() * Qe.T * sp.diag(*pi)
    ok(Qp[0:2, 0:2] == Qe[0:2, 0:2] and Qp[2:4, 2:4] == Qs[2:4, 2:4]
       and Qs[0, 1] == sp.Rational(351, 530) and Qp != Qs,
       "Q'_X = Q_X, Q'_Y = Q*_Y, q*_12 = 351/530, and Q' != Q*")


def part5():
    print("5. The gradient of the Perron branch")
    rng = np.random.default_rng(11)
    d = 5
    Q = rng.uniform(0, 1, (d, d)) * (rng.random((d, d)) < 0.6)
    np.fill_diagonal(Q, 0)
    Q -= np.diag(Q.sum(1))
    assert strongly_connected(Q)
    v = rng.normal(size=d)
    lam = lambda v: -np.max(np.linalg.eigvals(Q + np.diag(v)).real)
    h = 1e-6
    g = np.array([(lam(v + h * np.eye(d)[i]) - lam(v - h * np.eye(d)[i])) / (2 * h) for i in range(d)])
    ev, Vr = np.linalg.eig(Q + np.diag(v))
    r = np.real(Vr[:, np.argmax(ev.real)])
    ev2, Vl = np.linalg.eig((Q + np.diag(v)).T)
    l = np.real(Vl[:, np.argmax(ev2.real)])
    beta = l * r / (l @ r)
    ok(np.abs(g + beta).max() < 1e-6 and np.all(beta > 0),
       f"d lambda / d v_i = -(l o r)_i (max difference {np.abs(g + beta).max():.1e})")
    dt = np.linalg.det(np.eye(d - 1) - np.outer(np.ones(d - 1), beta[1:]))
    ok(abs(dt - beta[0]) < 1e-12, f"det(I - 1 beta'^T) = beta_1 = {beta[0]:.6f}")


def part6():
    print("6. Fibers on three states")
    rng = np.random.default_rng(5)
    res = []
    for trial in range(200):
        Q = rng.uniform(0.05, 1, (3, 3))
        np.fill_diagonal(Q, 0)
        Q -= np.diag(Q.sum(1))
        q = -np.diag(Q)
        w12, w23, w13 = Q[0, 1] * Q[1, 0], Q[1, 2] * Q[2, 1], Q[0, 2] * Q[2, 0]

        def F(x):
            y = q[1] - w12 / x
            z = w13 / (q[0] - x)
            return y * (q[2] - z) - w23
        lo, hi = w12 / q[1], q[0] - w13 / q[2]
        xs = np.linspace(lo, hi, 20001)[1:-1]
        vals = [F(x) for x in xs]
        sols = []
        for k in range(len(xs) - 1):
            if vals[k] == 0 or vals[k] * vals[k + 1] < 0:
                x = brentq(F, xs[k], xs[k + 1], xtol=1e-15)
                y = q[1] - w12 / x
                z = w13 / (q[0] - x)
                sols.append(np.array([[-q[0], x, q[0] - x], [q[1] - y, -q[1], y], [z, q[2] - z, -q[2]]]))
        Qs = time_reversal(Q)
        inset = all(min(np.abs(s - Q).max(), np.abs(s - Qs).max()) < 1e-7 for s in sols)
        hasQ = any(np.abs(s - Q).max() < 1e-7 for s in sols)
        hasQs = any(np.abs(s - Qs).max() < 1e-7 for s in sols)
        res.append((len(sols), inset, hasQ, hasQs))
    cnt = Counter(res)
    ok(all(r[1] and r[2] and r[3] for r in res),
       f"positive rates: every solution is Q or Q*, both occur, in all 200 cases {dict(cnt)}")
    rng = np.random.default_rng(11)
    cnt = []
    for trial in range(30):
        Q = rng.uniform(0, 1, (3, 3)) * (rng.random((3, 3)) < 0.75)
        np.fill_diagonal(Q, 0)
        Q -= np.diag(Q.sum(1))
        if not strongly_connected(Q):
            continue
        q = -np.diag(Q)
        w12, w23, w13 = Q[0, 1] * Q[1, 0], Q[1, 2] * Q[2, 1], Q[0, 2] * Q[2, 0]
        sols = []
        f = lambda p: [p[0] * (q[1] - p[1]) - w12, p[1] * (q[2] - p[2]) - w23, (q[0] - p[0]) * p[2] - w13]
        Qs = time_reversal(Q)
        starts = [tuple(np.clip([M[0, 1], M[1, 2], M[2, 0]], 0, q)) for M in (Q, Qs)]
        starts += list(itertools.product(np.linspace(0, q[0], 7), np.linspace(0, q[1], 7), np.linspace(0, q[2], 7)))
        for x0, y0, z0 in starts:
            if True:
                if True:
                    sol = so.least_squares(f, [x0, y0, z0], bounds=([0, 0, 0], q), xtol=1e-15, ftol=1e-15, gtol=1e-15)
                    if sol.cost < 1e-16:
                        x, y, z = sol.x
                        G = np.array([[-q[0], x, q[0] - x], [q[1] - y, -q[1], y], [z, q[2] - z, -q[2]]])
                        if strongly_connected(G) and not any(np.abs(G - s).max() < 1e-6 for s in sols):
                            sols.append(G)
        Qs = time_reversal(Q)
        good = all(min(np.abs(s - Q).max(), np.abs(s - Qs).max()) < 1e-5 for s in sols)
        cnt.append((len(sols), good))
    ok(len(cnt) > 0 and all(gd for _, gd in cnt) and all(n >= 1 for n, _ in cnt),
       f"irreducible with zero rates: {len(cnt)} generators, every irreducible solution found is Q or Q*; "
       f"numbers of solutions {Counter(n for n, _ in cnt)}")


def main():
    part1()
    part2()
    part3()
    part4()
    part5()
    part6()
    print(f"verify_reconstruction: all {CHECKS} checks passed")


if __name__ == "__main__":
    main()
