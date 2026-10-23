"""Checks for the weak field, Proposition `prop:weakfield` of the paper.

For a field xi in R^d put w(n) = exp(<xi, n>/N) P_N(n), and for a face F let M_F and M^xi_F be the
largest P_N(n) and w(n) over the compositions with support F. The proposition says:
  (a) w is the law of the composition under the path law tilted by exp(N^-1 sum_s xi_{X_s}), and
      exp(-|xi|) M_F <= M^xi_F <= exp(|xi|) M_F;
  (b) for a face with (H), M^xi_F = exp(<xi, alpha*_F>) M_F (1 + O(1/T + T^2/N)), and every
      maximizer of w on F sits at alpha*_F + O(1/T);
  (d) for irreducible Q, Z = E exp(<xi, n>/N) tends to exp(<xi, pi>) as T grows.
We check:
  A. (a) on a 3-state chain with N = 8 by listing all 3^8 words.
  B. (b) in the continuum on four faces: a pair of the path 1-2-3, the 3-arc of the 4-cycle, a
     3-state face that is not reversible, and the full face of K_3. The density f_T of
     Lemma 2.4 is computed by the torus integral of Lemma A.2 (the engine of
     verify_second_order.py) and maximized over alpha with and without the tilt. Completing the
     square as in the proof of Proposition 4.15(ii), with gamma_F replaced by gamma_F + xi_hat,
     suggests T (log max e^<xi,alpha> f_T - log max f_T - <xi, alpha*>) -> kappa with
     kappa = gamma . Sigma xi_hat + xi_hat . Sigma xi_hat / 2, and that the maximizer moves by
     Sigma (gamma + xi_hat) / T. We check both limits by Richardson extrapolation in T. The paper
     states only the order O(1/T), so these limits are a sharper test of the mechanism.
  C. (b) at finite N on the pair face, by an exact dynamic program of the chain at N = 20000,
     against the continuum values of B (they differ by O(T^2/N)).
  D. (d) by the transfer matrix at N = 10^6.
Every check is an assertion. Run: python -B verify_weak_field.py   (about a minute)
"""
import itertools
import math
import sys
from math import log, sqrt
from pathlib import Path

import numpy as np
from scipy.optimize import minimize_scalar

sys.path.insert(0, str(Path(__file__).resolve().parent))
from verify_second_order import consts_A, occupation_cov, perron, tilt_radii, torus_logf  # noqa: E402

checks = 0


def ok(cond, what):
    global checks
    assert cond, what
    checks += 1
    print(f'  ok  {what}', flush=True)


def face_data(A, q, mu):
    """alpha*, Sigma (coordinates alpha_2..alpha_k) and gamma = grad log C_F at alpha*."""
    A, q, mu = (np.asarray(x, float) for x in (A, q, mu))
    c = consts_A(A, q, mu)
    al = c['alpha']
    theta, r = tilt_radii(A, al)
    G = np.diag(1 / r) @ (A - np.diag(theta)) @ np.diag(r)
    Sigma = occupation_cov(G, al)[1:, 1:]
    k = len(al)
    gam = np.zeros(k - 1)
    eps = 1e-5
    for j in range(1, k):
        e = np.zeros(k)
        e[j], e[0] = 1.0, -1.0
        gam[j - 1] = (log(consts_A(A, q, mu, al + eps * e)['K']) - log(consts_A(A, q, mu, al - eps * e)['K'])) / (2 * eps)
    return al, Sigma, gam


def cont_max(A, q, mu, xi, T, al0):
    """max over alpha of log f_T(alpha) + <xi, alpha>, and the maximizer."""
    k = len(al0)
    K = (64 + 4 * int(6 * sqrt(T))) if k == 2 else (48 + int(9 * sqrt(T)))

    def full(x):
        return np.concatenate([[1 - np.sum(x)], x])

    def neg(x):
        a = full(np.atleast_1d(x))
        if np.min(a) <= 0:
            return 1e300
        return -(torus_logf(A, q, mu, a, T, K) + float(np.asarray(xi) @ a))
    if k == 2:
        r = minimize_scalar(neg, bounds=(al0[1] - 0.2, al0[1] + 0.2), method='bounded', options=dict(xatol=1e-11))
        return -r.fun, full(np.array([r.x]))
    # Newton's method with central differences, on the scale T^(-1/2) of the peak
    x = np.array(al0[1:], float)
    s = 0.02 / sqrt(T)
    E = np.eye(k - 1) * s
    for _ in range(8):
        f0 = -neg(x)
        g = np.array([(-neg(x + E[i]) + neg(x - E[i])) / (2 * s) for i in range(k - 1)])
        H = np.empty((k - 1, k - 1))
        for i in range(k - 1):
            for j in range(k - 1):
                H[i, j] = (-neg(x + E[i] + E[j]) + neg(x + E[i] - E[j]) + neg(x - E[i] + E[j]) - neg(x - E[i] - E[j])) / (4 * s * s)
        step = np.linalg.solve(H, -g)
        x = x + step
        if np.max(np.abs(step)) < 1e-12:
            break
    return -neg(x), full(x)


def check_a():
    print('\nA. Proposition (a): the tilt of the path law, by listing all words', flush=True)
    Q = np.array([[-2.2, 2.0, 0.2], [0.5, -1.5, 1.0], [1.5, 0.3, -1.8]])
    mu = np.array([0.5, 0.3, 0.2])
    xi = np.array([1.0, -0.5, 0.2])
    N, h = 8, 0.11
    P = np.eye(3) + h * Q
    law, tilted = {}, {}
    for w in itertools.product(range(3), repeat=N):
        pr = mu[w[0]] * np.prod([P[a, b] for a, b in zip(w, w[1:])])
        n = tuple(w.count(i) for i in range(3))
        law[n] = law.get(n, 0.0) + pr
        tilted[n] = tilted.get(n, 0.0) + pr * math.exp(sum(xi[s] for s in w) / N)
    worst = max(abs(tilted[n] - math.exp(float(xi @ np.array(n)) / N) * law[n]) for n in law)
    ok(worst < 1e-15, f'tilted path law summed by composition = exp(<xi,n>/N) P_N(n) on {len(law)} compositions (max error {worst:.1e})')
    nx = np.max(np.abs(xi))
    good = True
    for F in itertools.chain.from_iterable(itertools.combinations(range(3), k) for k in (1, 2, 3)):
        ns = [n for n in law if {i for i in range(3) if n[i] > 0} == set(F)]
        MF = max(law[n] for n in ns)
        MxF = max(tilted[n] for n in ns)
        good &= math.exp(-nx) * MF <= MxF * (1 + 1e-12) and MxF <= math.exp(nx) * MF * (1 + 1e-12)
    ok(good, 'exp(-|xi|) M_F <= M^xi_F <= exp(|xi|) M_F on all 7 faces')


FACES = {
    'pair {1,2} of the path 1-2-3': ([[0, 1], [1, 0]], [1, 2], [1 / 3, 1 / 3], [0.7, -0.4]),
    '3-arc of the 4-cycle': ([[0, 1, 0], [1, 0, 1], [0, 1, 0]], [2, 2, 2], [0.25] * 3, [0.3, -0.2, 0.5]),
    'non-reversible 3-state face': ([[0, 2.0, 0.2], [0.5, 0, 1.0], [1.5, 0.3, 0]], [2.2, 1.5, 1.8], [0.5, 0.3, 0.2], [1.0, -0.5, 0.2]),
    'full face of K_3': ([[0, 1, 1], [1, 0, 1], [1, 1, 0]], [2, 2, 2], [1 / 3] * 3, [0.0, 0.0, -1.5]),
}


def check_b():
    print('\nB. Proposition (b) in the continuum: tilted face maxima and their location', flush=True)
    Ts = [20.0, 40.0, 80.0, 160.0]
    for name, (A, q, mu, xi) in FACES.items():
        A, q, mu, xi = (np.asarray(x, float) for x in (A, q, mu, xi))
        al, Sigma, gam = face_data(A, q, mu)
        xh = xi[1:] - xi[0]
        kappa = float(gam @ Sigma @ xh + 0.5 * xh @ Sigma @ xh)
        shift = Sigma @ (gam + xh)
        ys, ds, ss = [], [], []
        for T in Ts:
            m0, a0 = cont_max(A, q, mu, np.zeros_like(xi), T, al)
            m1, a1 = cont_max(A, q, mu, xi, T, al)
            d = m1 - m0 - float(xi @ al)
            ds.append(d)
            ys.append(T * d)
            ss.append(T * (a1[1:] - al[1:]))
        ys = np.array(ys)
        r1 = 2 * ys[1:] - ys[:-1]
        r2 = (4 * r1[1:] - r1[:-1]) / 3
        ok(all(abs(ds[i + 1]) < abs(ds[i]) for i in range(len(ds) - 1)) and abs(ds[-1]) < 0.02,
           f'{name}: log M^xi - log M - <xi,alpha*> = {", ".join(f"{d:.5f}" for d in ds)} at T = 20, 40, 80, 160')
        ok(abs(r2[-1] - kappa) < 2e-3 * max(1.0, abs(kappa)),
           f'{name}: T times it -> {r2[-1]:.5f} (Richardson), kappa = {kappa:.5f}')
        ss = np.array(ss)
        s1 = 2 * ss[1:] - ss[:-1]
        ok(np.max(np.abs(s1[-1] - shift)) < 0.02 * max(1.0, np.max(np.abs(shift))),
           f'{name}: T (argmax - alpha*) -> {np.round(s1[-1], 4)}, Sigma (gamma + xi_hat) = {np.round(shift, 4)}')
    return


def pair_dp(qin, qtot, mu, h, N):
    """log P_N(c, N - c) for 1 <= c <= N-1, the chain on a face of 2 states (exact dynamic program)."""
    a = np.zeros(N + 1)
    b = np.zeros(N + 1)
    a[1], b[0] = mu[0], mu[1]
    s1, s2 = 1 - h * qtot[0], 1 - h * qtot[1]
    for _ in range(N - 1):
        na = np.empty_like(a)
        na[0] = 0.0
        na[1:] = a[:-1] * s1 + b[:-1] * h * qin[1]
        nb = a * h * qin[0] + b * s2
        a, b = na, nb
    c = np.arange(1, N)
    return c, np.log(a[1:N] + b[1:N])


def check_c():
    print('\nC. Proposition (b) at finite N: an exact dynamic program on the pair face', flush=True)
    A, q, mu, xi = FACES['pair {1,2} of the path 1-2-3']
    al, Sigma, gam = face_data(np.array(A, float), np.array(q, float), np.array(mu, float))
    N = 20000
    for T in (5.0, 10.0, 20.0):
        c, lp = pair_dp([1.0, 1.0], q, mu, T / N, N)
        al1 = c / N
        lw = lp + xi[0] * al1 + xi[1] * (1 - al1)
        d_disc = lw.max() - lp.max() - (xi[0] * al[0] + xi[1] * al[1])
        m0, _ = cont_max(np.array(A, float), np.array(q, float), np.array(mu, float), np.zeros(2), T, al)
        m1, _ = cont_max(np.array(A, float), np.array(q, float), np.array(mu, float), np.array(xi), T, al)
        d_cont = m1 - m0 - (xi[0] * al[0] + xi[1] * al[1])
        ok(abs(d_disc - d_cont) < 3 * T * T / N,
           f'T = {T:g}, N = {N}: discrete {d_disc:.6f}, continuum {d_cont:.6f}, |difference| {abs(d_disc - d_cont):.1e} < 3 T^2/N')
        cm = c[np.argmax(lw)] / N
        ok(abs(cm - al[0]) < 3 / T, f'T = {T:g}: the tilted maximizer has alpha_1 = {cm:.5f}, alpha*_1 = {al[0]:.5f}')


def check_d():
    print('\nD. Proposition (d): the normalizing sum for an irreducible chain', flush=True)
    Q = np.array([[-2.2, 2.0, 0.2], [0.5, -1.5, 1.0], [1.5, 0.3, -1.8]])
    mu = np.array([0.5, 0.3, 0.2])
    xi = np.array([1.0, -0.5, 0.2])
    w, V = np.linalg.eig(Q.T)
    pi_ = np.real(V[:, np.argmin(np.abs(w))])
    pi_ /= pi_.sum()
    N = 10 ** 6
    errs = []
    for T in (10.0, 20.0, 40.0, 80.0):
        D = np.diag(np.exp(xi / N))
        P = np.eye(3) + (T / N) * Q
        Z = float(mu @ D @ np.linalg.matrix_power(P @ D, N - 1) @ np.ones(3))
        errs.append(log(Z) - float(xi @ pi_))
    Te = np.array([10.0, 20.0, 40.0, 80.0]) * np.array(errs)
    ok(all(abs(errs[i + 1]) < abs(errs[i]) for i in range(3)) and abs(errs[-1]) < 0.01,
       f'log Z - <xi,pi> = {", ".join(f"{e:.5f}" for e in errs)} at T = 10, 20, 40, 80 (N = 10^6)')
    ok(abs(Te[-1] - Te[-2]) < 0.2 * abs(Te[-1]) + 1e-3, f'T (log Z - <xi,pi>) = {", ".join(f"{e:.4f}" for e in Te)}, of order 1')


def main():
    for step in (check_a, check_b, check_c, check_d):
        step()
    print(f'\nverify_weak_field: all {checks} checks passed', flush=True)


if __name__ == '__main__':
    main()
