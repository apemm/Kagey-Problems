"""Checks of the local law over the whole switching range, Paper C1 (problem131_chains.tex).

The chain has transition matrix P = I + hQ with h = T/N, and the paper's discrete functional is
J^(h)(alpha) = (1/h) sup_u sum_i alpha_i log(u_i / (P_F u)_i), with the constant C^(h)_F of
Section `sec:locallaw`. The exact laws are computed by a forward recursion over (count, last state)
in log space, which does not use the run expansion or the torus.

  A. The discrete torus formula of Lemma `lem:torus`. For two states (N = 30, h q_max up to 0.9)
     and for a non-reversible chain on three states (N = 9), the torus integral, computed by the
     trapezoid rule on circles of radius theta_2(alpha) and 1.5 theta_2(alpha), equals the exact
     law. Brute force over all paths checks the recursion for N <= 12.
  B. The discrete functional (Propositions `prop:discrete-rate`, `prop:discrete-variational` and
     Lemma `lem:discrete-hessian`). J^(h) >= J_F. The two forms of C^(h)_F, through the Hessian of
     J^(h) and through b(theta') and the Hessian H_h, agree, and C^(0)_F equals C_F computed from
     Definition `def:tilt`. On a face with exit rates, J^(h) - v.alpha is least at l o r for the
     Perron vectors of e^(h diag v)(I + hQ_F), with the value -(1/h) log rho, and at v = 0 the
     least point is alpha*_F with the value -(1/h) log(1 - h lambda_F) for every h.
  C. Theorem `thm:local`(b) for q12 = 1, q21 = 2, N = 4000 and two starts: the ratio R of the
     exact law to N^-1 T^(1/2) C^(h)_F e^(-T J^(h)) has T |R - 1| <= 0.25 at points of [0.45, 0.85]
     for T = 16, 63, 200, 400 and 1000 = N/4, while the continuum form gives T |R - 1| of order T
     at T >= 200. At T = 1600 (h q_max = 0.8) the bound is 0.3.
  D. Theorem `thm:facemax`(a) on the face {1, 2} of a chain on three states with exit rates: the
     exact face maximum over N^-1 T^(1/2) K^(h)_F (1 - h lambda_F)^N is within 10^-3 of 1 and the
     maximizer is within 0.2/T of alpha*_F, for T up to N/4. With K_F e^(-T lambda_F) in place of
     K^(h)_F (1 - h lambda_F)^N the ratio falls to 10^-56 at T = N/4, and for T <= 200 it tracks
     e^(-T^2 lambda_F^2 / 2N).
  E. Theorem `thm:local`(b) on the whole non-reversible chain on three states, N = 400, T = 20 and
     40: T |R - 1| <= 0.35.
  F. The term T^2/N after Theorem `thm:facemax`: (T J^(h) - T J_F) / ((T^2/2N) sum alpha_i
     (q_i - theta_i)^2) tends to 1 as h -> 0.

Every check is an assertion. Nothing in the paper is deduced from these numbers.
Needs numpy. Run:  py -I verify_full_range.py   (about 15 seconds)
"""
import itertools
import math

import numpy as np

CHECKS = 0
LOG0 = -np.inf


def ok(cond, what):
    global CHECKS
    if not cond:
        raise AssertionError(what)
    CHECKS += 1
    print('  ok   ', what, flush=True)


# ------------------------------------------------------------------ exact laws
def law_two(N, h, A, q, mu):
    """log P_N(n_1, N - n_1) on F = {0, 1}, killed on leaving F, indexed by n_1."""
    lp = [math.log(1.0 - h * q[0]), math.log(1.0 - h * q[1])]
    l01 = math.log(h * A[0][1])
    l10 = math.log(h * A[1][0])
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


def law_three(N, h, A, q, mu):
    """L[c1, c2] = log P_N(c1, c2, N - c1 - c2) on three states, killed on leaving."""
    P = np.array(A, float) * h
    for i in range(3):
        P[i, i] = 1.0 - h * q[i]
    with np.errstate(divide='ignore'):
        lP = np.log(P)
    f = np.full((3, N + 1, N + 1), LOG0)
    for s, (a, b) in enumerate(((1, 0), (0, 1), (0, 0))):
        if mu[s] > 0:
            f[s, a, b] = math.log(mu[s])
    for _ in range(N - 1):
        g = np.full_like(f, LOG0)
        for s in range(3):
            acc = np.full((N + 1, N + 1), LOG0)
            for r in range(3):
                if lP[r, s] > LOG0:
                    acc = np.logaddexp(acc, f[r] + lP[r, s])
            if s == 0:
                g[0, 1:, :] = acc[:-1, :]
            elif s == 1:
                g[1, :, 1:] = acc[:, :-1]
            else:
                g[2] = acc
        f = g
    return np.logaddexp(np.logaddexp(f[0], f[1]), f[2])


def brute(N, h, A, q, mu):
    k = len(mu)
    P = np.array(A, float) * h
    for i in range(k):
        P[i, i] = 1.0 - h * q[i]
    out = {}
    for path in itertools.product(range(k), repeat=N):
        pr = mu[path[0]]
        for s in range(N - 1):
            pr *= P[path[s], path[s + 1]]
        if pr > 0:
            c = tuple(path.count(i) for i in range(k))
            out[c] = out.get(c, 0.0) + pr
    return out


# ------------------------------------------------- the torus objects of Lemma A.2
def g_b(zp, A, mu):
    """g(z') and b(z') of Lemma lem:torus, for complex z' (state 0 plays state 1)."""
    A = np.asarray(A, float)
    a1, b1, Ap = A[0, 1:], A[1:, 0], A[1:, 1:]
    X = np.linalg.inv(np.diag(zp) - Ap)
    g = a1 @ X @ b1
    b = (mu[0] + np.asarray(mu[1:]) @ X @ b1) * (1.0 + a1 @ X @ np.ones(len(zp)))
    return g, b


def torus_law(n, h, A, q, mu, radii, M=64):
    """The discrete formula of Lemma lem:torus by the trapezoid rule with M points per circle."""
    k = len(n)
    p = 1.0 - h * np.asarray(q, float)
    phis = 2 * math.pi * np.arange(M) / M
    total = 0.0
    for idx in itertools.product(range(M), repeat=k - 1):
        zp = np.array([radii[j] * np.exp(1j * phis[idx[j]]) for j in range(k - 1)])
        g, b = g_b(zp, A, mu)
        val = (p[0] + h * g) ** (n[0] - 1) * b * np.prod(zp)
        for j in range(1, k):
            val *= (p[j] + h * zp[j - 1]) ** (n[j] - 1)
        total += val
    return (h ** (k - 1) * total / M ** (k - 1)).real


# ----------------------------------------------------------- the discrete functional
def ell(x, h):
    """-L_h(-x) = log(1 + h x)/h and its first two derivatives, with the value x at h = 0."""
    x = np.asarray(x, float)
    if h == 0:
        return x, np.ones_like(x), np.zeros_like(x)
    s = 1.0 + h * x
    return np.log(s) / h, 1.0 / s, -h / s ** 2


def rate(alpha, h, A, q, tol=1e-13):
    """(J^(h)(alpha), theta) by Newton's method on psi with psi_0 = 0."""
    A = np.asarray(A, float)
    q = np.asarray(q, float)
    alpha = np.asarray(alpha, float)
    k = len(alpha)

    def parts(psi):
        E = A * np.exp(psi[None, :] - psi[:, None])
        th = E.sum(axis=1)
        val, d1, d2 = ell(th - q, h)
        f = float(alpha @ val)
        D = E - np.diag(th)
        grad = (alpha * d1) @ D
        H = np.zeros((k, k))
        for i in range(k):
            S = np.zeros((k, k))
            for a in range(k):
                for c in range(k):
                    S[a, c] = E[i, a] * ((a == c) - (i == c)) - (i == a) * (E[i, c] - (i == c) * th[i])
            H += alpha[i] * (d1[i] * S + d2[i] * np.outer(D[i], D[i]))
        return f, grad, H, th

    psi = np.zeros(k)
    for _ in range(200):
        f, grad, H, th = parts(psi)
        step = np.linalg.solve(H[1:, 1:], -grad[1:])
        t = 1.0
        while True:
            new = psi.copy()
            new[1:] += t * step
            if parts(new)[0] <= f + 1e-4 * t * float(grad[1:] @ step) or t < 1e-12:
                break
            t *= 0.5
        psi = new
        if np.max(np.abs(t * step)) < tol:
            break
    f, grad, H, th = parts(psi)
    return -f, th


def hess_J(alpha, h, A, q, d=2e-3):
    alpha = np.asarray(alpha, float)
    m = len(alpha) - 1

    def J(x):
        return rate(np.concatenate([[1.0 - x.sum()], x]), h, A, q)[0]

    def fd(d):
        x0 = alpha[1:].copy()
        Hm = np.zeros((m, m))
        for i in range(m):
            for j in range(i, m):
                ei = np.zeros(m)
                ei[i] = d
                ej = np.zeros(m)
                ej[j] = d
                Hm[i, j] = Hm[j, i] = (J(x0 + ei + ej) - J(x0 + ei - ej) - J(x0 - ei + ej)
                                       + J(x0 - ei - ej)) / (4 * d * d)
        return Hm

    return (4 * fd(d / 2) - fd(d)) / 3


def null_vectors(theta, A):
    M = np.asarray(A, float) - np.diag(theta)
    w, V = np.linalg.eig(M)
    r = np.abs(V[:, np.argmax(w.real)].real)
    w2, U = np.linalg.eig(M.T)
    l = np.abs(U[:, np.argmax(w2.real)].real)
    return r, l / (l @ r)


def C_hessian(alpha, h, A, q, mu):
    """C^(h)_F = c_h (mu.r)(l.1) sqrt(det Hess J^(h) / (2 pi)^(k-1)), the definition in the paper."""
    alpha = np.asarray(alpha, float)
    q = np.asarray(q, float)
    k = len(alpha)
    _, th = rate(alpha, h, A, q)
    r, l = null_vectors(th, A)
    c = float(np.sum(alpha / (1.0 - h * q + h * th)))
    det = np.linalg.det(hess_J(alpha, h, A, q))
    return c * float(np.dot(mu, r)) * float(l.sum()) * math.sqrt(det / (2 * math.pi) ** (k - 1))


def C_torus(alpha, h, A, q, mu, d=2e-3):
    """Lemma lem:discrete-hessian(c): b(theta')/((2 pi)^((k-1)/2) prod(p_i + h theta_i) sqrt det H_h)."""
    alpha = np.asarray(alpha, float)
    q = np.asarray(q, float)
    m = len(alpha) - 1
    _, th = rate(alpha, h, A, q)

    def Psi(zp):
        g, _ = g_b(zp, A, mu)
        return float(alpha @ ell(np.concatenate([[g.real], zp]) - q, h)[0])

    z0 = th[1:].copy()

    def fd(d):
        Hm = np.zeros((m, m))
        for i in range(m):
            for j in range(i, m):
                ei = np.zeros(m)
                ei[i] = d
                ej = np.zeros(m)
                ej[j] = d
                Hm[i, j] = Hm[j, i] = (Psi(z0 + ei + ej) - Psi(z0 + ei - ej) - Psi(z0 - ei + ej)
                                       + Psi(z0 - ei - ej)) / (4 * d * d)
        return Hm

    Hm = (4 * fd(d / 2) - fd(d)) / 3
    _, b = g_b(z0, A, mu)
    pref = float(np.prod(1.0 - h * q + h * th))
    return b.real / ((2 * math.pi) ** (m / 2) * pref * math.sqrt(np.linalg.det(Hm)))


def C_definition(alpha, A, mu):
    """C_F of Definition def:tilt, through Z_alpha, Gamma_alpha and Sigma_alpha."""
    alpha = np.asarray(alpha, float)
    k = len(alpha)
    _, th = rate(alpha, 0.0, A, np.asarray(A, float).sum(axis=1))
    r, l = null_vectors(th, A)
    R = np.diag(r)
    Qhat = np.linalg.inv(R) @ (np.asarray(A, float) - np.diag(th)) @ R
    one = np.ones(k)
    Z = np.linalg.inv(np.outer(one, alpha) - Qhat) - np.outer(one, alpha)
    D = np.diag(alpha)
    G = D @ Z + Z.T @ D
    Sig = G[1:, 1:]
    return float(np.dot(mu, r)) * float(l.sum()) / ((2 * math.pi) ** ((k - 1) / 2) * math.sqrt(np.linalg.det(Sig)))


# ---------------------------------------------------------------------- the parts
A2 = [[0.0, 1.0], [2.0, 0.0]]
q2 = np.array([1.0, 2.0])
A3 = np.array([[0.0, 2.0, 0.7], [0.5, 0.0, 1.0], [1.5, 0.3, 0.0]])
q3 = A3.sum(axis=1)
mu3 = np.array([0.5, 0.3, 0.2])


def part_a():
    print('A. The discrete torus formula of Lemma lem:torus')
    for mu in ([0.5, 0.5], [1.0, 0.0]):
        for N in (8, 12):
            exact = brute(N, 0.3, A2, q2, mu)
            L = law_two(N, 0.3, A2, q2, mu)
            err = max(abs(math.log(exact[(n1, N - n1)]) - L[n1]) for n1 in range(N + 1) if (n1, N - n1) in exact)
            ok(err < 1e-12, f'two states, mu = {mu}, N = {N}: recursion = brute force, max log error {err:.1e}')
    N = 30
    for hq in (0.2, 0.6, 0.9):
        h = hq / q2.max()
        L = law_two(N, h, A2, q2, [0.5, 0.5])
        err = 0.0
        for n1 in (1, 7, 15, 29):
            th = rate([n1 / N, 1 - n1 / N], h, A2, q2)[1]
            for s in (th[1], 1.5 * th[1]):
                v = torus_law([n1, N - n1], h, A2, q2, [0.5, 0.5], [s], M=128)
                err = max(err, abs(v / math.exp(L[n1]) - 1))
        ok(err < 1e-9, f'two states, N = {N}, h q_max = {hq}: torus integral = exact law, radii theta_2 and'
           f' 1.5 theta_2, max rel error {err:.1e}')
    N = 9
    h = 0.25
    exact = brute(N, h, A3, q3, mu3)
    err = 0.0
    for n in ((3, 3, 3), (2, 4, 3), (1, 1, 7), (5, 2, 2)):
        th = rate(np.array(n) / N, h, A3, q3)[1]
        v = torus_law(list(n), h, A3, q3, mu3, th[1:], M=32)
        err = max(err, abs(v / exact[n] - 1))
    L = law_three(N, h, A3, q3, mu3)
    err2 = max(abs(math.log(exact[n]) - L[n[0], n[1]]) for n in exact)
    ok(err2 < 1e-12, f'three states, N = {N}: recursion = brute force, max log error {err2:.1e}')
    ok(err < 1e-9, f'three states, N = {N}, h = {h}: torus integral = exact law at 4 compositions, max rel error {err:.1e}')


def part_b():
    print('B. The discrete functional and its constant')
    mu = [0.5, 0.5]
    worst = 0.0
    for h in (0.0, 0.05, 0.25, 0.4):
        for a in (0.5, 0.6, 0.8):
            al = [a, 1 - a]
            Jh = rate(al, h, A2, q2)[0]
            J0 = rate(al, 0.0, A2, q2)[0]
            ok(Jh >= J0 - 1e-12, f'h = {h}, alpha_1 = {a}: J^(h) = {Jh:.6f} >= J_F = {J0:.6f}')
            c1 = C_hessian(al, h, A2, q2, mu)
            c2 = C_torus(al, h, A2, q2, mu)
            worst = max(worst, abs(c1 / c2 - 1))
    ok(worst < 1e-7, f'two states: the two forms of C^(h)_F agree for h <= 0.4, max rel difference {worst:.1e}')
    worst = 0.0
    for al in ([0.26, 0.412, 0.328], [0.3, 0.3, 0.4], [0.2, 0.6, 0.2]):
        for h in (0.0, 0.1, 0.25):
            worst = max(worst, abs(C_hessian(al, h, A3, q3, mu3) / C_torus(al, h, A3, q3, mu3) - 1))
        c0 = C_hessian(al, 0.0, A3, q3, mu3)
        cd = C_definition(al, A3, mu3)
        ok(abs(c0 / cd - 1) < 1e-7, f'three states, alpha = {al}: C^(0)_F = {c0:.8f} = C_F of Definition def:tilt')
    ok(worst < 1e-7, f'three states, non-reversible: the two forms of C^(h)_F agree for h <= 0.25, max rel difference {worst:.1e}')
    AF, qF = A3[:2, :2], q3[:2]
    lam = -max(np.linalg.eigvals(AF - np.diag(qF)).real)
    r0, l0 = null_vectors(qF - lam, AF)
    astar = l0 * r0
    for h in (0.01, 0.1, 0.3):
        J = lambda a: rate([a, 1 - a], h, AF, qF)[0]  # noqa: E731
        grid = np.linspace(0.05, 0.95, 181)
        amin = grid[int(np.argmin([J(a) for a in grid]))]
        val = J(astar[0])
        ok(abs(val + math.log(1 - h * lam) / h) < 1e-10 and abs(amin - astar[0]) < 0.006,
           f'face {{1,2}}, h = {h}: least value {val:.10f} = -(1/h) log(1 - h lambda_F) at alpha*_F = {astar[0]:.4f} (grid {amin:.3f})')
        v = np.array([0.4, -0.3])
        Mv = np.diag(np.exp(h * v)) @ (np.eye(2) + h * (AF - np.diag(qF)))
        w, V = np.linalg.eig(Mv)
        rho = max(w.real)
        r = np.abs(V[:, np.argmax(w.real)].real)
        w2, U = np.linalg.eig(Mv.T)
        l = np.abs(U[:, np.argmax(w2.real)].real)
        av = l * r / (l @ r)
        Jv = lambda a: J(a) - v @ np.array([a, 1 - a])  # noqa: E731
        amin = grid[int(np.argmin([Jv(a) for a in grid]))]
        ok(abs(Jv(av[0]) + math.log(rho) / h) < 1e-10 and abs(amin - av[0]) < 0.006,
           f'face {{1,2}}, h = {h}, field v = (0.4, -0.3): least value -(1/h) log rho at l o r = {av[0]:.4f}')


def part_c():
    print('C. The local law over the whole range, two states, N = 4000')
    N = 4000
    lo, hi = int(0.45 * N), int(0.85 * N)
    for mu in ([0.5, 0.5], [2 / 3, 1 / 3]):
        for T in (16, 63, 200, 400, 1000):
            h = T / N
            L = law_two(N, h, A2, q2, mu)
            dev, devc = [], []
            for n1 in range(lo, hi + 1, 100):
                al = np.array([n1 / N, 1 - n1 / N])
                Ch = C_hessian(al, h, A2, q2, mu)
                Jh = rate(al, h, A2, q2)[0]
                R = math.exp(L[n1] - (-math.log(N) + 0.5 * math.log(T) + math.log(Ch) - T * Jh))
                dev.append(T * abs(R - 1))
                C0 = C_hessian(al, 0.0, A2, q2, mu)
                J0 = rate(al, 0.0, A2, q2)[0]
                Rc = math.exp(L[n1] - (-math.log(N) + 0.5 * math.log(T) + math.log(C0) - T * J0))
                devc.append(T * abs(Rc - 1))
            ok(max(dev) <= 0.25, f'mu = {[round(x, 3) for x in mu]}, T = {T:4d}: max T|R - 1| = {max(dev):.3f}'
               f' (continuum form: {max(devc):.3g})')
            if T >= 200:
                ok(max(devc) > 0.1 * T, f'  the continuum form fails at T = {T}: max T|R - 1| = {max(devc):.3g}')
    T = 1600
    h = T / N
    L = law_two(N, h, A2, q2, [0.5, 0.5])
    dev = []
    for n1 in range(lo, hi + 1, 200):
        al = np.array([n1 / N, 1 - n1 / N])
        R = math.exp(L[n1] - (-math.log(N) + 0.5 * math.log(T) + math.log(C_hessian(al, h, A2, q2, [0.5, 0.5]))
                              - T * rate(al, h, A2, q2)[0]))
        dev.append(T * abs(R - 1))
    ok(max(dev) <= 0.3, f'T = 1600, h q_max = 0.8: max T|R - 1| = {max(dev):.3f}')


def part_d():
    print('D. Face maxima over the whole range, face {1,2} of a chain on three states, N = 4000')
    AF, qF, muF = A3[:2, :2], q3[:2], mu3[:2]
    lam = -max(np.linalg.eigvals(AF - np.diag(qF)).real)
    r0, l0 = null_vectors(qF - lam, AF)
    astar = l0 * r0
    KF = C_hessian(astar, 0.0, AF, qF, muF)
    N = 4000
    for T in (16, 63, 200, 400, 1000):
        h = T / N
        L = law_two(N, h, AF, qF, muF)
        i = int(np.argmax(L[1:N])) + 1
        KFh = C_hessian(astar, h, AF, qF, muF)
        new = -math.log(N) + 0.5 * math.log(T) + math.log(KFh) + N * math.log(1 - h * lam)
        old = -math.log(N) + 0.5 * math.log(T) + math.log(KF) - T * lam
        rn, ro = math.exp(L[i] - new), math.exp(L[i] - old)
        ok(abs(rn - 1) < 1e-3 and T * abs(i / N - astar[0]) <= 0.2,
           f'T = {T:4d}: M_F/new = {rn:.5f}, T |alpha_hat - alpha*| = {T * abs(i / N - astar[0]):.3f},'
           f' M_F/old = {ro:.4g}, e^(-T^2 lambda^2/2N) = {math.exp(-T * T * lam * lam / (2 * N)):.4g}')


def part_e():
    print('E. The local law on the whole non-reversible chain on three states, N = 400')
    N = 400
    w, V = np.linalg.eig((A3 - np.diag(q3)).T)
    pi = np.abs(V[:, np.argmax(w.real)].real)
    pi /= pi.sum()
    for T in (20, 40):
        h = T / N
        L = law_three(N, h, A3, q3, mu3)
        dev = []
        for a in (pi, np.array([0.3, 0.3, 0.4]), np.array([0.2, 0.6, 0.2])):
            n = np.round(a * N).astype(int)
            n[2] = N - n[0] - n[1]
            al = n / N
            R = math.exp(L[n[0], n[1]] - (-2 * math.log(N) + math.log(T) + math.log(C_hessian(al, h, A3, q3, mu3))
                                         - T * rate(al, h, A3, q3)[0]))
            dev.append(T * abs(R - 1))
        ok(max(dev) <= 0.35, f'T = {T}: max T|R - 1| = {max(dev):.3f} at three points')


def part_f():
    print('F. The second-order term of the continuum exponent')
    N = 4000
    prev = None
    for T in (16, 63, 200):
        h = T / N
        rows = []
        for a1 in (0.45, 0.55, 0.85):
            al = np.array([a1, 1 - a1])
            J0, th0 = rate(al, 0.0, A2, q2)
            Jh = rate(al, h, A2, q2)[0]
            rows.append((T * Jh - T * J0) / ((T * T / (2 * N)) * float(al @ (q2 - th0) ** 2)))
        dev = max(abs(x - 1) for x in rows)
        ok(prev is None or dev > prev, f'h = {h:.4f}: ratios {", ".join(f"{x:.4f}" for x in rows)}, distance to 1 grows with h')
        if T == 16:
            ok(dev < 0.01, f'  at h = {h} the ratio is within 1% of 1')
        prev = dev


if __name__ == '__main__':
    part_a()
    part_b()
    part_c()
    part_d()
    part_e()
    part_f()
    print(f'verify_full_range: all {CHECKS} checks passed')
