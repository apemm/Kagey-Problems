# o2_lib.py -- shared routines for the C1 full-range local law (O2).
#
# Exact law of the composition of the chain P = I + hQ (killed on leaving a face F),
# by a log-space forward recursion and, for two states, by Good's run sum; the
# discrete Donsker-Varadhan rate J_h = I_h / h; the constant C_F^(h) by two
# independent routes (Hessian of J_h, and the torus objects g, b of app_torus).
# h = 0 gives the continuum objects J_F and C_F of Paper C1.
# Imported by the o2_*.py scripts; run those with: py -I <script>.py  (numpy only).
import itertools
import math

import numpy as np

LOG0 = -np.inf


# ---------------------------------------------------------------- exact laws
def dp_two_state_log(N, h, A, q, mu):
    """log P_N(n_1, N - n_1) for the chain on F = {0, 1} killed on leaving F.

    A: 2x2 rates inside F (zero diagonal), q: exit rates (including the rates
    out of F), mu: start masses of the two states. Returns an array of length
    N + 1 indexed by n_1 (n_1 in {0, N} are the vertices).
    """
    lp = [math.log(1.0 - h * q[0]), math.log(1.0 - h * q[1])]
    l01 = math.log(h * A[0][1]) if A[0][1] > 0 else LOG0
    l10 = math.log(h * A[1][0]) if A[1][0] > 0 else LOG0
    # f0[c]: log prob of c visits to state 0 so far and current state 0; f1 likewise.
    f0 = np.full(N + 1, LOG0)
    f1 = np.full(N + 1, LOG0)
    if mu[0] > 0:
        f0[1] = math.log(mu[0])
    if mu[1] > 0:
        f1[0] = math.log(mu[1])
    for _ in range(N - 1):
        g0 = np.full(N + 1, LOG0)
        g0[1:] = np.logaddexp(f0[:-1] + lp[0], f1[:-1] + l10)
        g1 = np.logaddexp(f1 + lp[1], f0 + l01)
        f0, f1 = g0, g1
    return np.logaddexp(f0, f1)


def good_two_state_log(N, n1, h, A, q, mu):
    """log P_N(n_1, N - n_1) from Good's run expansion (Lemma lem:runs), n_1, n_2 >= 1."""
    n2 = N - n1
    lp1, lp2 = math.log(1.0 - h * q[0]), math.log(1.0 - h * q[1])
    la, lb, lh = math.log(A[0][1]), math.log(A[1][0]), math.log(h)
    lg = math.lgamma

    def lbin(n, m):  # log C(n-1, m-1)
        return lg(n) - lg(m) - lg(n - m + 1)

    terms = []
    for start in (0, 1):
        if mu[start] <= 0:
            continue
        for m1 in range(1, n1 + 1):
            for m2 in (m1 - 1, m1, m1 + 1):
                if m2 < 1 or m2 > n2:
                    continue
                if start == 0 and m2 not in (m1, m1 - 1):
                    continue
                if start == 1 and m1 not in (m2, m2 - 1):
                    continue
                M = m1 + m2
                if start == 0:
                    s01 = m1 if m2 == m1 else m1 - 1
                    s10 = M - 1 - s01
                else:
                    s10 = m2 if m1 == m2 else m2 - 1
                    s01 = M - 1 - s10
                terms.append(math.log(mu[start]) + s01 * la + s10 * lb + (M - 1) * lh
                             + lbin(n1, m1) + lbin(n2, m2) + (n1 - m1) * lp1 + (n2 - m2) * lp2)
    t = np.array(terms)
    mx = t.max()
    return mx + math.log(np.exp(t - mx).sum())


def brute_log(N, h, A, q, mu):
    """Brute force over all paths in F of length N: dict composition -> log prob."""
    k = len(mu)
    P = np.array(A, float) * h
    for i in range(k):
        P[i, i] = 1.0 - h * q[i]
    out = {}
    for path in itertools.product(range(k), repeat=N):
        pr = mu[path[0]]
        for s in range(N - 1):
            pr *= P[path[s], path[s + 1]]
        if pr == 0:
            continue
        c = tuple(path.count(i) for i in range(k))
        out[c] = out.get(c, 0.0) + pr
    return {c: math.log(v) for c, v in out.items()}


def dp_three_state_log(N, h, A, q, mu):
    """L[c1, c2] = log P_N(c1, c2, N - c1 - c2) for a chain on three states (killed
    on leaving if q exceeds the row sums of A)."""
    k = 3
    P = np.array(A, float) * h
    for i in range(k):
        P[i, i] = 1.0 - h * q[i]
    with np.errstate(divide="ignore"):
        lP = np.log(P)
    f = np.full((k, N + 1, N + 1), LOG0)
    if mu[0] > 0:
        f[0, 1, 0] = math.log(mu[0])
    if mu[1] > 0:
        f[1, 0, 1] = math.log(mu[1])
    if mu[2] > 0:
        f[2, 0, 0] = math.log(mu[2])
    for _ in range(N - 1):
        g = np.full_like(f, LOG0)
        for s in range(k):
            acc = np.full((N + 1, N + 1), LOG0)
            for r in range(k):
                if lP[r, s] == LOG0:
                    continue
                acc = np.logaddexp(acc, f[r] + lP[r, s])
            if s == 0:
                g[0, 1:, :] = acc[:-1, :]
            elif s == 1:
                g[1, :, 1:] = acc[:, :-1]
            else:
                g[2] = acc
        f = g
    out = f[0]
    for s in range(1, k):
        out = np.logaddexp(out, f[s])
    return out


# ------------------------------------------------- discrete DV rate J_h = I_h/h
def _ell(x, h):
    """ell_h(x) = log(1 + h x)/h with ell_0(x) = x, and its first two derivatives."""
    x = np.asarray(x, float)
    if h == 0:
        return x, np.ones_like(x), np.zeros_like(x)
    s = 1.0 + h * x
    return np.log(s) / h, 1.0 / s, -h / s ** 2


def rate(alpha, h, A, q, tol=1e-13, maxit=200):
    """(J_h(alpha), theta, psi) on a face with inside rates A (zero diagonal), exit rates q.

    J_h(alpha) = -min_psi sum_i alpha_i ell_h(theta_i(psi) - q_i),
    theta_i(psi) = sum_j A_ij exp(psi_j - psi_i), psi_0 = 0. This is
    (1/h) sup_u sum_i alpha_i log(u_i / (P_F u)_i) with u = exp(psi).
    """
    A = np.asarray(A, float)
    q = np.asarray(q, float)
    alpha = np.asarray(alpha, float)
    k = len(alpha)
    psi = np.zeros(k)

    def parts(psi):
        E = A * np.exp(psi[None, :] - psi[:, None])
        th = E.sum(axis=1)
        val, d1, d2 = _ell(th - q, h)
        f = float(alpha @ val)
        Dth = E - np.diag(th)  # d theta_i / d psi_l
        grad = (alpha * d1) @ Dth
        H = np.zeros((k, k))
        for i in range(k):
            S = np.zeros((k, k))
            for l in range(k):
                for m in range(k):
                    S[l, m] = (E[i, l] * ((l == m) - (i == m))
                               - (i == l) * (E[i, m] - (i == m) * th[i]))
            H += alpha[i] * (d1[i] * S + d2[i] * np.outer(Dth[i], Dth[i]))
        return f, grad, H, th

    for _ in range(maxit):
        f, grad, H, th = parts(psi)
        g = grad[1:]
        step = np.linalg.solve(H[1:, 1:], -g)
        t = 1.0
        while True:
            new = psi.copy()
            new[1:] += t * step
            if parts(new)[0] <= f + 1e-4 * t * float(g @ step) or t < 1e-12:
                break
            t *= 0.5
        psi = new
        if np.max(np.abs(t * step)) < tol:
            break
    f, grad, H, th = parts(psi)
    return -f, th, psi


def hess_J(alpha, h, A, q, d=2e-3):
    """Hessian of J_h in the coordinates alpha_2..alpha_k (central differences
    with one Richardson step)."""
    H1 = _hess_J_fd(alpha, h, A, q, d)
    H2 = _hess_J_fd(alpha, h, A, q, d / 2)
    return (4 * H2 - H1) / 3


def _hess_J_fd(alpha, h, A, q, d):
    alpha = np.asarray(alpha, float)
    m = len(alpha) - 1

    def J(x):
        return rate(np.concatenate([[1.0 - x.sum()], x]), h, A, q)[0]

    x0 = alpha[1:].copy()
    Hm = np.zeros((m, m))
    for i in range(m):
        for j in range(i, m):
            ei = np.zeros(m); ei[i] = d
            ej = np.zeros(m); ej[j] = d
            Hm[i, j] = Hm[j, i] = (J(x0 + ei + ej) - J(x0 + ei - ej) - J(x0 - ei + ej)
                                   + J(x0 - ei - ej)) / (4 * d * d)
    return Hm


def perron_lr(theta, A):
    """Positive right/left null vectors r, l of A - diag(theta), with l.r = 1."""
    M = np.asarray(A, float) - np.diag(theta)
    w, V = np.linalg.eig(M)
    r = np.abs(V[:, np.argmax(w.real)].real)
    w2, U = np.linalg.eig(M.T)
    l = np.abs(U[:, np.argmax(w2.real)].real)
    return r, l / (l @ r)


def constant_hessian_route(alpha, h, A, q, mu):
    """C_F^(h)(alpha) = c_h (mu.r)(l.1) sqrt(det Hess J_h / (2 pi)^(k-1))."""
    alpha = np.asarray(alpha, float)
    q = np.asarray(q, float)
    k = len(alpha)
    J, th, psi = rate(alpha, h, A, q)
    r, l = perron_lr(th, A)
    c = float(np.sum(alpha / (1.0 - h * (q - th))))
    det = np.linalg.det(hess_J(alpha, h, A, q))
    return c * float(np.dot(mu, r)) * float(l.sum()) * math.sqrt(det / (2 * math.pi) ** (k - 1))


def _g_b(zp, A, mu):
    A = np.asarray(A, float)
    a1, b1, Ap = A[0, 1:], A[1:, 0], A[1:, 1:]
    X = np.linalg.inv(np.diag(zp) - Ap)
    g = float(a1 @ X @ b1)
    b = float((mu[0] + np.asarray(mu[1:]) @ X @ b1) * (1.0 + a1 @ X @ np.ones(len(zp))))
    return g, b


def constant_torus_route(alpha, h, A, q, mu, d=2e-3):
    """C_F^(h) from the torus: b(theta')/((2 pi)^((k-1)/2) prod_i(p_i + h theta_i) sqrt(det H_h)).

    H_h is the Hessian in z' of Psi_h(z') = alpha_1 ell_h(g(z') - q_1) + sum_j alpha_j
    ell_h(z_j - q_j) at z' = theta', by central differences with one Richardson step. Also returns the
    gradient there (it should vanish) and |g(theta') - theta_1| (should vanish).
    """
    alpha = np.asarray(alpha, float)
    q = np.asarray(q, float)
    m = len(alpha) - 1
    J, th, psi = rate(alpha, h, A, q)

    def Psi(zp):
        g, _ = _g_b(zp, A, mu)
        val, _, _ = _ell(np.concatenate([[g], zp]) - q, h)
        return float(alpha @ val)

    z0 = th[1:].copy()

    def fd(d):
        grad = np.zeros(m)
        Hm = np.zeros((m, m))
        for i in range(m):
            ei = np.zeros(m); ei[i] = d
            grad[i] = (Psi(z0 + ei) - Psi(z0 - ei)) / (2 * d)
            for j in range(i, m):
                ej = np.zeros(m); ej[j] = d
                Hm[i, j] = Hm[j, i] = (Psi(z0 + ei + ej) - Psi(z0 + ei - ej) - Psi(z0 - ei + ej)
                                       + Psi(z0 - ei - ej)) / (4 * d * d)
        return grad, Hm

    g1, H1 = fd(d)
    g2, H2 = fd(d / 2)
    grad, Hm = (4 * g2 - g1) / 3, (4 * H2 - H1) / 3
    g, b = _g_b(z0, A, mu)
    pref = float(np.prod(1.0 - h * q + h * th))
    C = b / ((2 * math.pi) ** (m / 2) * pref * math.sqrt(np.linalg.det(Hm)))
    return C, grad, abs(g - th[0])
