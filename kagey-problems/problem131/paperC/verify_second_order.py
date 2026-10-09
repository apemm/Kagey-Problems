"""Checks for Sections 2, 4 and 5 of Paper C (the second-order theory).

The model is the chain X_1..X_N with transition matrix I + hQ, h = T/N, and
P_N(n) is the probability that the composition of the N visits is n. For a face
F we write A for the rates inside F, q for the total exit rates of its states and
mu for the start restricted to F.

We compute P_N(n) in 2 independent ways.
Method A (the run expansion of Lemma 2.3). The weights W(m) are built by a
dynamic program over run counts, and the sum over m is done in log space. The
same table gives the continuum density f_T of Lemma 2.4.
Method B (a discrete torus integral). The generating function of the
composition, after the substitution 1/x_i = 1 - h q_i + h z_i and one residue,
is an integral over a torus of dimension k-1. It is exact for every N, and the
trapezoid rule converges geometrically. The continuum density f_T has the torus
form of Lemma A.2, which we also code.
For small N both are compared with a direct dynamic program of the chain and
with an enumeration of all words.

The constants K_F and C_F(alpha) of Definition 4.1 are also computed in 2 ways.
Method A uses the Perron vectors, the tilted generator and its fundamental
matrix in double precision. Method B uses 30-digit arithmetic, the Perron root
Lambda(theta) of Q_F + diag(theta) and its Hessian, which is Sigma.

Run with python -B verify_second_order.py, or add --full for the second crossing
of the directed 3-cycle at N = 10^8 and the continuum value of c_F on the whole
4-cycle.
"""
import argparse
import itertools
import math
import sys
import time
from fractions import Fraction
from math import cos, log, pi, sin, sqrt

import mpmath as mp
import numpy as np
import sympy as sp
from scipy.optimize import brentq, minimize, minimize_scalar
from scipy.special import gammaln

FAILS = []
mp.mp.dps = 30


def check(label, ok, detail):
    print(('  ok    ' if ok else '  FAIL  ') + label + ': ' + detail, flush=True)
    if not ok:
        FAILS.append(label)


def tol_of(printed):
    """Half a unit in the last printed digit."""
    s = printed.lstrip('+-')
    mant = s.split('e')[0]
    exp10 = int(s.split('e')[1]) if 'e' in s else 0
    dec = len(mant.split('.')[1]) if '.' in mant else 0
    return 0.5 * 10.0 ** (exp10 - dec) * (1 + 1e-9) + 1e-15


def agree(label, printed, values, extra=''):
    """Every value in the dict rounds to the printed number."""
    target = float(printed)
    t = tol_of(printed)
    ok = all(abs(float(v) - target) <= t for v in values.values())
    shown = ', '.join(f'{k} {float(v):.10g}' for k, v in values.items())
    check(label, ok, f'paper {printed}; {shown}{extra}')


# ---------------------------------------------------------------- models

def cycle_Q(d):
    Q = np.zeros((d, d))
    for i in range(d):
        Q[i, (i + 1) % d] += 1
        Q[i, (i - 1) % d] += 1
    np.fill_diagonal(Q, -Q.sum(1))
    return Q


def complete_Q(d):
    Q = np.ones((d, d))
    np.fill_diagonal(Q, 0)
    np.fill_diagonal(Q, -Q.sum(1))
    return Q


def random_gen(seed=7):
    """The random non-reversible generator of ledger_C5.md (seed 7)."""
    rng = np.random.default_rng(seed)
    Q = rng.uniform(0.2, 2.0, (4, 4))
    np.fill_diagonal(Q, 0)
    np.fill_diagonal(Q, -Q.sum(1))
    return Q


def face(Q, F, mu):
    F = list(F)
    A = np.array(Q, float)[np.ix_(F, F)].copy()
    np.fill_diagonal(A, 0.0)
    q = -np.diag(np.array(Q, float))[F]
    return A, q, np.array(mu, float)[F]


# ---------------------------------------------------------------- method A: run expansion

class RunFace:
    """W(m) for all m in {0..mmax}^k, by a dynamic program over run counts."""

    def __init__(self, A, q, mu, mmax):
        A = np.asarray(A, float)
        self.k = k = A.shape[0]
        self.q, self.mu, self.mmax = np.asarray(q, float), np.asarray(mu, float), mmax
        self.s = s = A.max() if A.max() > 0 else 1.0      # W(m) = Wsc(m) s^(M-1)
        As = A / s
        shape = (mmax + 1,) * k
        size = (mmax + 1) ** k
        coords = np.array(np.unravel_index(np.arange(size), shape), dtype=np.int32)
        tot = coords.sum(0)
        strides = [(mmax + 1) ** (k - 1 - j) for j in range(k)]
        W = np.zeros((k, size))                  # W[j, m]: words with run counts m ending in j
        for j in range(k):
            e = [0] * k
            e[j] = 1
            W[j, np.ravel_multi_index(e, shape)] = self.mu[j]
        order = np.argsort(tot, kind='stable')
        bounds = np.searchsorted(tot[order], np.arange(k * mmax + 2))
        for M in range(2, k * mmax + 1):
            layer = order[bounds[M]:bounds[M + 1]]
            for j in range(k):
                sel = layer[coords[j, layer] >= 1]
                pred = sel - strides[j]
                acc = np.zeros(len(sel))
                for i in range(k):
                    if As[i, j] != 0:
                        acc += As[i, j] * W[i, pred]
                W[j, sel] = acc
        self.Wsc = W.sum(0).reshape(shape)

    def _contract(self, vecs):
        shifts = [np.max(v[np.isfinite(v)]) for v in vecs]
        X = self.Wsc
        for i, v in enumerate(vecs):
            ev = np.where(np.isfinite(v), np.exp(v - shifts[i]), 0.0)
            X = np.tensordot(X, ev, axes=([0], [0]))
        return log(float(X)) + sum(shifts)

    def logP(self, n, h):
        """log P_N(n) for n with every coordinate >= 1; n may be real (analytic in n)."""
        if min(n) < 1:
            return -1e300
        m = np.arange(self.mmax + 1)
        jj = np.arange(1, self.mmax + 1, dtype=float)
        vecs = []
        for i in range(self.k):
            ni = float(n[i])
            v = np.full(self.mmax + 1, -np.inf)
            ok = (m >= 1) & (m <= ni)
            mm = m[ok]
            cl = np.concatenate([[0.0], np.cumsum(np.log(np.maximum(ni - jj, 1e-300)))])
            v[ok] = (mm * log(h * self.s) + cl[mm - 1] - gammaln(mm)
                     + (ni - mm) * np.log1p(-h * self.q[i]))
            vecs.append(v)
        return self._contract(vecs) - log(h * self.s)

    def logH(self, t):
        m = np.arange(1, self.mmax + 1)
        vecs = []
        for i in range(self.k):
            v = np.full(self.mmax + 1, -np.inf)
            v[1:] = (m - 1) * log(t[i]) - gammaln(m) + m * log(self.s)
            vecs.append(v)
        return self._contract(vecs) - log(self.s)

    def logf(self, alpha, T):
        t = T * np.asarray(alpha, float)
        return (self.k - 1) * log(T) - float(self.q @ t) + self.logH(t)


# ---------------------------------------------------------------- method B: torus integrals

def clog1p(x):
    """Complex log(1+x), accurate for small |x|."""
    x = np.asarray(x, dtype=complex)
    out = np.empty_like(x)
    small = np.abs(x) < 1e-3
    xs = x[small]
    s = np.zeros_like(xs)
    p = np.ones_like(xs)
    for j in range(1, 9):
        p = p * xs
        s = s + ((-1) ** (j + 1)) * p / j
    out[small] = s
    out[~small] = np.log(1 + x[~small])
    return out


def tilt_radii(A, alpha):
    """theta(alpha) = A r / r where r maximizes the sup in I_F (Newton, w_0 = 0)."""
    k = len(alpha)
    al = np.asarray(alpha, float) / np.sum(alpha)
    w = np.zeros(k)

    def parts(w):
        E = al[:, None] * A * np.exp(w[None, :] - w[:, None])
        return E.sum(), E.sum(0) - E.sum(1), E
    f, g, E = parts(w)
    for _ in range(200):
        if np.max(np.abs(g[1:])) < 1e-14 * max(1.0, f):
            break
        H = -(E + E.T)
        np.fill_diagonal(H, 0)
        np.fill_diagonal(H, -H.sum(1))
        st = np.linalg.solve(H[1:, 1:], g[1:])
        t = 1.0
        while True:
            wn = w.copy()
            wn[1:] -= t * st
            fn, gn, En = parts(wn)
            if fn <= f + 1e-15 * abs(f) or t < 1e-12:
                break
            t /= 2
        w, f, g, E = wn, fn, gn, En
    r = np.exp(w)
    return (A @ r) / r, r


def torus_logP(A, q, mu, n, h, M=None, rho=None):
    """log P_N(n) by the discrete torus integral (exact for every N)."""
    A = np.asarray(A, float)
    k = len(q)
    n = np.asarray(n, dtype=float)
    if k == 1:
        return log(mu[0]) + (n[0] - 1) * math.log1p(-h * q[0])
    if rho is None:
        rho, _ = tilt_radii(A, n / n.sum())
    a1, b1, Ap = A[0, 1:], A[1:, 0], A[1:, 1:]
    rp = rho[1:]
    T = h * n.sum()
    if M is None:
        M = int(max(24, 14 * np.sqrt(T * max(1.0, rho.max())) + 8))
        M += M % 2
    ph = 2 * np.pi * np.arange(M) / M
    grids = np.meshgrid(*([ph] * (k - 1)), indexing='ij')
    Zf = np.stack([rp[j] * np.exp(1j * grids[j]) for j in range(k - 1)], axis=-1).reshape(-1, k - 1)
    P = Zf.shape[0]
    Mat = np.empty((P, k - 1, k - 1), dtype=complex)
    Mat[:] = -Ap
    idx = np.arange(k - 1)
    Mat[:, idx, idx] += Zf
    rhs = np.empty((P, k - 1, 2), dtype=complex)
    rhs[:, :, 0] = b1
    rhs[:, :, 1] = 1.0
    sol = np.linalg.solve(Mat, rhs)
    Xb, X1 = sol[:, :, 0], sol[:, :, 1]
    g = Xb @ a1
    R = (mu[0] + Xb @ mu[1:]) * (1 + X1 @ a1)
    with np.errstate(divide='ignore'):
        logI = np.log(R + 0j) + (n[0] - 1) * clog1p(h * (g - q[0]))
    for j in range(k - 1):
        logI = logI + (n[j + 1] - 1) * clog1p(h * (Zf[:, j] - q[j + 1])) + np.log(Zf[:, j])
    s = np.max(logI.real)
    val = np.mean(np.exp(logI - s))
    return (k - 1) * log(h) + s + log(val.real)


def torus_logP_conv(A, q, mu, n, h):
    """Discrete torus integral, grid doubled until 2 values agree to 1e-12."""
    rho, _ = tilt_radii(np.asarray(A, float), np.asarray(n, float) / np.sum(n))
    T = h * np.sum(n)
    M = int(max(24, 14 * np.sqrt(T * max(1.0, rho.max())) + 8))
    M += M % 2
    v0 = torus_logP(A, q, mu, n, h, M, rho)
    while True:
        v1 = torus_logP(A, q, mu, n, h, 2 * M, rho)
        if abs(v1 - v0) < 1e-12 or (2 * M) ** (len(q) - 1) > 3e6:
            return v1
        M, v0 = 2 * M, v1


def torus_logH(A, mu, t, rho_p, K, chunk=150000):
    """log H(t) by Lemma A.2 (trapezoid rule with K points per circle)."""
    A = np.asarray(A, float)
    k = A.shape[0]
    a1, b1, Ap = A[0, 1:], A[1:, 0], A[1:, 1:]
    mu1, mup = mu[0], mu[1:]
    ph = 2 * np.pi * np.arange(K) / K
    P = K ** (k - 1)
    Z0 = rho_p.astype(complex)
    g0 = a1 @ np.linalg.solve(np.diag(Z0) - Ap, b1)
    shift = t[0] * g0.real + float(np.real(Z0) @ t[1:])
    acc = 0.0 + 0.0j
    for s0 in range(0, P, chunk):
        ii = np.arange(s0, min(P, s0 + chunk))
        digs = np.array(np.unravel_index(ii, (K,) * (k - 1))).T
        Zs = rho_p[None, :] * np.exp(1j * ph[digs])
        p = Zs.shape[0]
        Mats = np.zeros((p, k - 1, k - 1), complex)
        for i in range(k - 1):
            Mats[:, i, i] = Zs[:, i]
        Mats -= Ap[None, :, :]
        Xb = np.linalg.solve(Mats, np.broadcast_to(b1, (p, k - 1))[..., None])[..., 0]
        Xt = np.linalg.solve(np.transpose(Mats, (0, 2, 1)), np.broadcast_to(a1, (p, k - 1))[..., None])[..., 0]
        g = Xb @ a1
        Rz = (mu1 + Xb @ mup) * (1 + Xt.sum(1))
        acc += np.sum(np.exp(t[0] * g + Zs @ t[1:] - shift) * Rz * np.prod(Zs, axis=1))
    return log((acc / P).real) + shift


def torus_logf(A, q, mu, alpha, T, K):
    alpha = np.asarray(alpha, float)
    rho, _ = tilt_radii(np.asarray(A, float), alpha)
    k = len(alpha)
    return (k - 1) * log(T) - T * float(np.asarray(q) @ alpha) + torus_logH(A, np.asarray(mu, float), T * alpha, rho[1:], K)


# ---------------------------------------------------------------- brute force

def dp_law(Q, mu, h, N):
    """Composition law by a forward dynamic program (dict n -> probability)."""
    d = len(mu)
    P = np.eye(d) + h * np.asarray(Q, float)
    cur = {}
    for i in range(d):
        if mu[i]:
            c = [0] * d
            c[i] = 1
            cur[(tuple(c), i)] = cur.get((tuple(c), i), 0.0) + mu[i]
    for _ in range(N - 1):
        nxt = {}
        for (c, i), p in cur.items():
            for j in range(d):
                if P[i, j] == 0:
                    continue
                cc = list(c)
                cc[j] += 1
                key = (tuple(cc), j)
                nxt[key] = nxt.get(key, 0.0) + p * P[i, j]
        cur = nxt
    law = {}
    for (c, i), p in cur.items():
        law[c] = law.get(c, 0.0) + p
    return law


def word_law(Q, mu, h, N):
    """Composition law by listing all d^N words."""
    d = len(mu)
    P = np.eye(d) + h * np.asarray(Q, float)
    law = {}
    for w in itertools.product(range(d), repeat=N):
        p = mu[w[0]]
        for a, b in zip(w, w[1:]):
            p *= P[a, b]
        c = tuple(w.count(i) for i in range(d))
        law[c] = law.get(c, 0.0) + p
    return law


# ---------------------------------------------------------------- constants, method A

def perron(M):
    w, V = np.linalg.eig(M)
    i = int(np.argmax(w.real))
    r = np.abs(V[:, i].real)
    w2, V2 = np.linalg.eig(M.T)
    j = int(np.argmax(w2.real))
    l = np.abs(V2[:, j].real)
    return w[i].real, r, l


def occupation_cov(G, pi_):
    """Gamma = D Z + Z^T D with Z = (1 pi^T - G)^(-1) - 1 pi^T."""
    k = len(pi_)
    Pi = np.outer(np.ones(k), pi_)
    Z = np.linalg.inv(Pi - G) - Pi
    D = np.diag(pi_)
    return D @ Z + Z.T @ D


def consts_A(A, q, mu, alpha=None):
    """lambda_F, alpha*, K_F (or C_F(alpha) and I_F(alpha)) and det Sigma, from the fundamental matrix."""
    A = np.asarray(A, float)
    q = np.asarray(q, float)
    mu = np.asarray(mu, float)
    k = len(q)
    if alpha is None:
        s, r, l = perron(A - np.diag(q))
        lam = -s
        l = l / (l @ r)
        al = l * r
        theta = q - lam
        I = lam
    else:
        al = np.asarray(alpha, float)
        theta, r = tilt_radii(A, al)
        l = al / r
        I = float((q - theta) @ al)
        lam = None
    if k == 1:
        return dict(lam=q[0], alpha=np.ones(1), K=mu[0], detS=1.0, I=q[0])
    G = np.diag(1 / r) @ (A - np.diag(theta)) @ np.diag(r)
    Gam = occupation_cov(G, al)
    dS = np.linalg.det(Gam[1:, 1:])
    K = float(mu @ r) * float(l.sum()) * (2 * pi) ** (-(k - 1) / 2) * dS ** (-0.5)
    return dict(lam=lam, alpha=al, K=K, detS=dS, I=I, r=r, l=l, theta=theta)


# ---------------------------------------------------------------- constants, method B (mpmath)

def mp_perron(M):
    k = M.rows
    Mf = np.array([[float(M[i, j]) for j in range(k)] for i in range(k)])
    s0 = max(np.linalg.eigvals(Mf).real)
    if k == 1:
        return M[0, 0], [mp.mpf(1)], [mp.mpf(1)]
    Id = mp.eye(k)
    lam = mp.findroot(lambda s: mp.det(M - s * Id), (mp.mpf(s0) - mp.mpf('1e-6'), mp.mpf(s0) + mp.mpf('1e-6')),
                      solver='secant', tol=mp.mpf(10) ** (-2 * mp.mp.dps + 10), maxsteps=200)
    B = M - lam * Id
    rr = mp.lu_solve(B[1:, 1:], mp.matrix([-B[i, 0] for i in range(1, k)]))
    r = [mp.mpf(1)] + [rr[i] for i in range(k - 1)]
    Bt = B.T
    ll = mp.lu_solve(Bt[1:, 1:], mp.matrix([-Bt[i, 0] for i in range(1, k)]))
    l = [mp.mpf(1)] + [ll[i] for i in range(k - 1)]
    return lam, r, l


class MPFace:
    """Lambda(theta) = Perron root of Q_F + diag(theta); Sigma = its Hessian in theta_2..theta_k."""

    def __init__(self, A, q, mu):
        self.k = len(q)
        self.A = mp.matrix([[mp.mpf(repr(float(x))) if not isinstance(x, mp.mpf) else x for x in row] for row in np.asarray(A, float)])
        self.q = [mp.mpf(repr(float(x))) for x in q]
        self.mu = [mp.mpf(repr(float(x))) for x in mu]

    def QF(self, theta):
        M = mp.matrix(self.k, self.k)
        for i in range(self.k):
            for j in range(self.k):
                M[i, j] = self.A[i, j]
            M[i, i] = -self.q[i] + theta[i]
        return M

    def grad(self, theta):
        lam, r, l = mp_perron(self.QF(theta))
        lr = mp.fsum(l[i] * r[i] for i in range(self.k))
        return lam, [l[i] * r[i] / lr for i in range(self.k)], r, l

    def hess(self, theta):
        k = self.k
        eps = mp.mpf(10) ** (-(mp.mp.dps // 4))
        L0 = mp_perron(self.QF(theta))[0]

        def Lv(a, sa, b, sb):
            th = list(theta)
            th[a] += sa * eps
            th[b] += sb * eps
            return mp_perron(self.QF(th))[0]
        H = mp.matrix(k - 1, k - 1)
        for a in range(1, k):
            H[a - 1, a - 1] = (Lv(a, 1, a, 0) + Lv(a, -1, a, 0) - 2 * L0) / eps ** 2
            for b in range(a + 1, k):
                v = (Lv(a, 1, b, 1) - Lv(a, 1, b, -1) - Lv(a, -1, b, 1) + Lv(a, -1, b, -1)) / (4 * eps ** 2)
                H[a - 1, b - 1] = H[b - 1, a - 1] = v
        return H

    def theta_of(self, alpha):
        k = self.k
        alpha = [mp.mpf(repr(float(x))) for x in alpha]
        s = mp.fsum(alpha)
        alpha = [x / s for x in alpha]
        th = [mp.mpf(0)] * k
        for _ in range(100):
            lam, g, r, l = self.grad(th)
            F = mp.matrix([g[i] - alpha[i] for i in range(1, k)])
            if mp.norm(F) < mp.mpf(10) ** (-(mp.mp.dps - 8)):
                break
            step = mp.lu_solve(self.hess(th), F)
            t = mp.mpf(1)
            while True:
                thn = [th[0]] + [th[i] - t * step[i - 1] for i in range(1, k)]
                Fn = mp.matrix([self.grad(thn)[1][i] - alpha[i] for i in range(1, k)])
                if mp.norm(Fn) < mp.norm(F) or t < mp.mpf('1e-6'):
                    break
                t /= 2
            th = thn
        return th

    def data(self, alpha=None):
        k = self.k
        th = [mp.mpf(0)] * k if alpha is None else self.theta_of(alpha)
        lam, g, r, l = self.grad(th)
        lr = mp.fsum(l[i] * r[i] for i in range(k))
        l = [x / lr for x in l]
        al = [l[i] * r[i] for i in range(k)]
        if k > 1:
            Sig = self.hess(th)
            detS = mp.det(Sig)
        else:
            Sig, detS = None, mp.mpf(1)
        # I_F(alpha) = Legendre transform: <alpha, theta> - Lambda(theta), with theta measured from 0
        I = mp.fsum(al[i] * th[i] for i in range(k)) - lam
        C = mp.fsum(self.mu[i] * r[i] for i in range(k)) * mp.fsum(l) * (2 * mp.pi) ** (-mp.mpf(k - 1) / 2) / mp.sqrt(detS)
        return dict(lam=-lam, alpha=al, K=C, detS=detS, I=I, Sigma=Sig)


# ---------------------------------------------------------------- Paper A's polynomial

def S_ab(a, b, u):
    """S_{a,b}(u) = P_{a+b}(a)/P_{a+b}(0) for Paper A's walk, exactly (u rational or float)."""
    tot = 0
    for m1 in range(1, a + 1):
        for m2 in (m1 - 1, m1, m1 + 1):
            if 1 <= m2 <= b:
                c = 2 if m1 == m2 else 1
                tot += c * math.comb(a - 1, m1 - 1) * math.comb(b - 1, m2 - 1) * u ** (m1 + m2 - 1)
    return tot


# ======================================================================== checks

def check_engines():
    print('\nLemma 2.3 and Lemma A.1: the run expansion against brute force and the torus', flush=True)
    worst = {'run-DP': 0.0, 'torus-DP': 0.0, 'DP-words': 0.0}
    cells = [(cycle_Q(4), 6, 0.05), (cycle_Q(4), 10, 0.2), (random_gen(7), 6, 0.03), (random_gen(7), 10, 0.03)]
    mu = np.ones(4) / 4
    for Q, N, h in cells:
        law = dp_law(Q, mu, h, N)
        if N == 6:
            wl = word_law(Q, mu, h, N)
            worst['DP-words'] = max(worst['DP-words'], max(abs(wl[c] / law[c] - 1) for c in law if law[c] > 1e-280))
        faces = {}
        sample = set(list(law)[::7])                 # the torus is slower, so it sees every 7th composition
        for c, p in law.items():
            if p < 1e-280:
                continue
            F = tuple(i for i in range(4) if c[i] > 0)
            if len(F) == 1:
                pe = mu[F[0]] * (1 + h * Q[F[0], F[0]]) ** (N - 1)
                worst['run-DP'] = max(worst['run-DP'], abs(pe / p - 1))
                continue
            if F not in faces:
                faces[F] = RunFace(*face(Q, F, mu), mmax=N)
            nn = [c[i] for i in F]
            worst['run-DP'] = max(worst['run-DP'], abs(math.exp(faces[F].logP(nn, h)) / p - 1))
            if c in sample:
                worst['torus-DP'] = max(worst['torus-DP'], abs(math.exp(torus_logP_conv(*face(Q, F, mu), nn, h)) / p - 1))
    check('run expansion = dynamic program (paper: 7e-15)', worst['run-DP'] < 2e-14,
          f"max relative difference {worst['run-DP']:.1e} on the 4-cycle and the seed-7 generator, N = 6, 10")
    check('discrete torus = dynamic program', worst['torus-DP'] < 1e-11, f"max relative difference {worst['torus-DP']:.1e}")
    check('dynamic program = all 4^6 words', worst['DP-words'] < 1e-13, f"max relative difference {worst['DP-words']:.1e}")
    # continuum: Lemma A.2 against the series H(t), face {0,1,2} of the seed-7 generator
    Q = random_gen(7)
    A, q, m = face(Q, [0, 1, 2], mu)
    rf = RunFace(A, q, m, mmax=120)
    rng = np.random.default_rng(3)
    worst_t = 0.0
    for _ in range(5):
        t = rng.uniform(0.5, 12, 3)
        rho_p = A[1:, 1:].sum(1) + 1.0          # any radii with s(A' - diag rho') < 0
        worst_t = max(worst_t, abs(math.expm1(torus_logH(A, m, t, rho_p, K=96) - rf.logH(t))))
    check('torus representation = run sum H(t) (paper: 7e-13)', worst_t < 1e-12,
          f'max relative difference {worst_t:.1e} at 5 random t')


def check_constants():
    print('\nProposition 4.2 and Corollaries 4.10, 4.11, 5.1: the constants', flush=True)
    # Paper A
    Q2 = complete_Q(2)
    mu2 = np.array([0.5, 0.5])
    cA = consts_A(*face(Q2, [0, 1], mu2))
    cB = MPFace(*face(Q2, [0, 1], mu2)).data()
    check('Paper A: K_{1,2} = sqrt(2/pi), det Sigma = 1/4', abs(cA['K'] - sqrt(2 / pi)) < 1e-13 and abs(float(cB['K']) - sqrt(2 / pi)) < 1e-13
          and abs(cA['detS'] - 0.25) < 1e-13 and abs(float(cB['detS']) - 0.25) < 1e-13,
          f"K: A {cA['K']:.15f}, B {float(cB['K']):.15f}; det: A {cA['detS']:.15f}, B {float(cB['detS']):.15f}")
    agree('c_0 = (1/2) log(pi/8) = b_2 = left end of the K_3 window', '-0.4673558',
          {'closed': 0.5 * log(pi / 8), 'A: -log(K12/K1)': -log(cA['K'] / 0.5), 'B': -float(mp.log(cB['K'] / mp.mpf('0.5')))})
    # Paper B: complete graphs
    worst = 0.0
    for d in range(3, 7):
        Q = complete_Q(d)
        mu = np.ones(d) / d
        for k in range(2, d + 1):
            cA = consts_A(*face(Q, range(k), mu))
            cB = MPFace(*face(Q, range(k), mu)).data()
            Kc = k ** (k + 0.5) * (4 * pi) ** (-(k - 1) / 2) / d
            dSc = 2 ** (k - 1) * k ** (1 - 2 * k)
            ak = 0.5 * log(4 * pi) - (k + 0.5) / (k - 1) * log(k)
            b = -log(cA['K'] / (1 / d)) / (k - 1)      # b_FG with Delta = delta = k - 1 and G a vertex
            worst = max(worst, abs(cA['K'] / Kc - 1), abs(float(cB['K']) / Kc - 1), abs(cA['detS'] / dSc - 1),
                        abs(float(cB['detS']) / dSc - 1), abs(cA['lam'] - (d - k)), abs(b - ak))
    check('Paper B: K_F, det Sigma, lambda_F = d-k and b = a_k on K_d, d = 3..6', worst < 1e-11, f'max relative error {worst:.1e}')
    # Paper B's D(alpha) at random interior points
    rng = np.random.default_rng(11)
    worst = 0.0
    for d, k in [(3, 3), (4, 3), (4, 4), (5, 4)]:
        Q = complete_Q(d)
        mu = np.ones(d) / d
        al = rng.dirichlet(np.ones(k) * 3)
        A, q, m = face(Q, range(k), mu)
        cA = consts_A(A, q, m, al)
        cB = MPFace(A, q, m).data(al)
        S = np.sqrt(al).sum()
        Dc = S ** (k / 2 + 1) * np.prod(al) ** (-0.75) * (4 * pi) ** (-(k - 1) / 2) / d
        worst = max(worst, abs(cA['K'] / Dc - 1), abs(float(cB['K']) / Dc - 1), abs(cA['I'] - (d - S * S)), abs(float(cB['I']) - (d - S * S)))
    check("Paper B's D(alpha) and I_F(alpha) = d - (sum sqrt(alpha_i))^2", worst < 1e-9, f'max error {worst:.1e} at 4 random interior points')
    # weighted Cayley formula by listing all spanning trees
    worst = 0.0
    for k in range(3, 6):
        x = rng.uniform(0.3, 2.0, k)
        edges = list(itertools.combinations(range(k), 2))
        tot = 0.0
        for T in itertools.combinations(edges, k - 1):
            parent = list(range(k))

            def root(a):
                while parent[a] != a:
                    a = parent[a]
                return a
            ok = True
            for a, b in T:
                ra, rb = root(a), root(b)
                if ra == rb:
                    ok = False
                    break
                parent[ra] = rb
            if ok:
                tot += np.prod([x[a] * x[b] for a, b in T])
        worst = max(worst, abs(tot / (np.prod(x) * x.sum() ** (k - 2)) - 1))
    check('weighted Cayley formula (all spanning trees listed)', worst < 1e-13, f'max relative error {worst:.1e}, k = 3, 4, 5')
    # the 4-cycle
    Q4 = cycle_Q(4)
    mu4 = np.ones(4) / 4
    out = {}
    for name, F in [('pair', [0, 1]), ('arc3', [0, 1, 2]), ('C4', [0, 1, 2, 3])]:
        out[name] = (consts_A(*face(Q4, F, mu4)), MPFace(*face(Q4, F, mu4)).data())
    closed = {'pair': 1 / sqrt(2 * pi), 'arc3': (4 + 3 * sqrt(2)) / (4 * pi), 'C4': 8 / pi ** 1.5}
    worst = max(max(abs(a['K'] / closed[n] - 1), abs(float(b['K']) / closed[n] - 1)) for n, (a, b) in out.items())
    check('4-cycle: K_pair = 1/sqrt(2 pi), K_arc3 = (4+3 sqrt2)/(4 pi), K_C4 = 8/pi^(3/2)', worst < 1e-12, f'max relative error {worst:.1e}')
    check('4-cycle: det Sigma = 1/512 on C_4', abs(out['C4'][0]['detS'] * 512 - 1) < 1e-12 and abs(float(out['C4'][1]['detS']) * 512 - 1) < 1e-12,
          f"A {out['C4'][0]['detS']:.15g}, B {float(out['C4'][1]['detS']):.15g}")
    agree('log(K_arc3/K_vertex) on the 4-cycle', '0.964591',
          {'closed': log((4 + 3 * sqrt(2)) / pi), 'A': log(out['arc3'][0]['K'] / 0.25), 'B': float(mp.log(out['arc3'][1]['K'] * 4))})
    # arcs of a long cycle, and the whole cycle
    d = 10
    Q = cycle_Q(d)
    mu = np.ones(d) / d
    worst = 0.0
    Karc = {}
    for k in range(1, d):
        th = pi / (k + 1)
        Kc = 2 / (d * (k + 1)) * (1 + cos(th)) ** 2 / sin(th) ** 3 * ((k + 1) / (2 * pi)) ** ((k - 1) / 2)
        if k == 1:
            Karc[k] = (1 / d, 1 / d)
            continue
        cA = consts_A(*face(Q, range(k), mu))
        cB = MPFace(*face(Q, range(k), mu)).data() if k <= 6 else None
        worst = max(worst, abs(cA['K'] / Kc - 1), abs(cA['lam'] - (2 - 2 * cos(th))))
        if cB is not None:
            worst = max(worst, abs(float(cB['K']) / Kc - 1))
        Karc[k] = (cA['K'], Kc)
    check('K_arc(k) and lambda_k = 2 - 2cos(pi/(k+1)) on C_10, k = 2..9', worst < 1e-11, f'max relative error {worst:.1e}')
    worst = 0.0
    for dd in range(3, 9):
        Q = cycle_Q(dd)
        mu = np.ones(dd) / dd
        cA = consts_A(*face(Q, range(dd), mu))
        worst = max(worst, abs(cA['K'] / (dd ** ((dd + 2) / 2) * (4 * pi) ** (-(dd - 1) / 2)) - 1))
    check('K_{C_d} = d^((d+2)/2) (4 pi)^(-(d-1)/2), d = 3..8', worst < 1e-11, f'max relative error {worst:.1e}')
    # Table 1, row C_d: lambda_k and tau_k, and the arc offsets b_k of the notes (not printed in the paper)
    lam = lambda k: 2 - 2 * cos(pi / (k + 1))
    tab = {2: ('1', '1', '-0.4673558'), 3: ('0.585786', '2.414214', '-0.9379218'), 4: ('0.381966', '4.906280', '-1.3514657'),
           5: ('0.267949', '8.770636', '-1.7011216'), 6: ('0.198062', '14.308827', '-2.0012059'),
           7: ('0.152241', '21.823898', '-2.2632478'), 8: ('0.120615', '31.619377', '-2.4955119')}
    for k, (pl, pt, pb) in tab.items():
        dk = lam(k - 1) - lam(k)
        b_closed = 0.5 * log(dk) - log(Karc[k][1] / Karc[k - 1][1])
        b_num = 0.5 * log(dk) - log(Karc[k][0] / Karc[k - 1][0])
        lam_num = -perron(face(cycle_Q(10), range(k), np.ones(10))[0] - 2 * np.eye(k))[0]
        agree(f'Table 1, row C_d, k = {k}: lambda_k', pl, {'closed': lam(k), 'eigen': lam_num})
        agree(f'Table 1, row C_d, k = {k}: tau_k', pt, {'closed': 1 / dk, 'eigen': 1 / (lam(k - 1) - lam_num) if k > 1 else 1})
        agree(f'arcs of C_d, k = {k}: b_k (notes)', pb, {'closed': b_closed, 'numeric K': b_num})
    # Proposition 4.2(a): det Sigma det Hess I = 1, at random points of non-reversible faces
    worst = 0.0
    QR = random_gen(7)
    for F in ([0, 1, 2], [0, 1, 2, 3]):
        A, q, m = face(QR, F, np.ones(4) / 4)
        mf = MPFace(A, q, m)
        for _ in range(2):
            al = rng.dirichlet(np.ones(len(F)) * 4)
            cA = consts_A(A, q, m, al)
            cB = mf.data(al)
            # Hessian of I by central differences of I computed by method A
            k = len(F)

            def Ival(x):
                a = np.concatenate([[1 - x.sum()], x])
                return consts_A(A, q, m, a)['I']
            x0 = al[1:]

            def hess(e):
                H = np.zeros((k - 1, k - 1))
                for i in range(k - 1):
                    for j in range(k - 1):
                        ei = np.eye(k - 1)[i] * e
                        ej = np.eye(k - 1)[j] * e
                        H[i, j] = (Ival(x0 + ei + ej) - Ival(x0 + ei - ej) - Ival(x0 - ei + ej) + Ival(x0 - ei - ej)) / (4 * e * e)
                return H
            H = (4 * hess(1e-4) - hess(2e-4)) / 3          # Richardson removes the e^2 error
            worst = max(worst, abs(cA['detS'] * np.linalg.det(H) - 1), abs(float(cB['detS']) / cA['detS'] - 1), abs(float(cB['K']) / cA['K'] - 1))
    check('Proposition 4.2(a): det Sigma det Hess I = 1; methods A and B agree on C_F(alpha)', worst < 1e-6,
          f'max deviation {worst:.1e} at 4 random points of the seed-7 faces (finite differences)')
    # Proposition 4.2(b): the tree formula on random reversible faces
    worst = 0.0
    for k in range(3, 7):
        nu = rng.uniform(0.5, 2, k)
        S = rng.uniform(0.2, 2, (k, k))
        S = (S + S.T) / 2
        S *= rng.uniform(size=(k, k)) < 0.8
        S = np.triu(S, 1) + np.triu(S, 1).T
        for i in range(k - 1):                        # keep it connected
            S[i, i + 1] = S[i + 1, i] = max(S[i, i + 1], 0.3)
        A = S / nu[:, None]                            # nu_i q_ij = S_ij is symmetric
        q = A.sum(1) + rng.uniform(0, 1, k)            # some rate leaves the face
        m = rng.uniform(0.1, 1, k)
        al = rng.dirichlet(np.ones(k) * 3)
        cA = consts_A(A, q, m, al)
        c = np.sqrt(np.outer(al, al)) * A * np.sqrt(np.outer(nu, 1 / nu))
        Lap = np.diag(c.sum(1)) - c
        tau = np.linalg.det(Lap[1:, 1:])
        r = np.sqrt(al / nu)
        l = al / r
        Ct = float(m @ r) * float(l.sum()) * (4 * pi) ** (-(k - 1) / 2) * sqrt(tau) / np.prod(al)
        dSt = 2 ** (k - 1) * np.prod(al) ** 2 / tau
        It = float(q @ al) - c.sum()
        worst = max(worst, abs(cA['K'] / Ct - 1), abs(cA['detS'] / dSt - 1), abs(cA['I'] - It))
    check('Proposition 4.2(b): tree formula on random reversible faces, k = 3..6', worst < 1e-9, f'max error {worst:.1e}')


def check_pair_identity():
    print('\nProposition 4.9: the exact pair identity (exact rational arithmetic)', flush=True)
    bad = 0
    total = 0
    # 4-cycle, pair {0,1}, and a random symmetric pair with equal exit rates inside a 4-state chain
    Q1 = [[-2, 1, 0, 1], [1, -2, 1, 0], [0, 1, -2, 1], [1, 0, 1, -2]]
    Q2 = [[-3, Fraction(3, 2), Fraction(1, 2), 1], [Fraction(3, 2), -3, Fraction(3, 2), 0],
          [Fraction(1, 3), 1, Fraction(-7, 3), 1], [1, 1, 1, -3]]
    for Q, mu, h in [(Q1, [Fraction(1, 4)] * 4, Fraction(1, 7)), (Q2, [Fraction(1, 5), Fraction(1, 5), Fraction(1, 2), Fraction(1, 10)], Fraction(1, 11))]:
        a = Fraction(Q[0][1])
        qq = -Fraction(Q[0][0])
        u = a * h / (1 - qq * h)
        d = 4
        P = [[(1 if i == j else 0) + h * Fraction(Q[i][j]) for j in range(d)] for i in range(d)]
        for N in range(2, 10):
            cur = {}
            for i in range(d):
                c = [0] * d
                c[i] = 1
                cur[(tuple(c), i)] = Fraction(mu[i])
            for _ in range(N - 1):
                nxt = {}
                for (c, i), p in cur.items():
                    for j in range(d):
                        if P[i][j]:
                            cc = list(c)
                            cc[j] += 1
                            nxt[(tuple(cc), j)] = nxt.get((tuple(cc), j), 0) + p * P[i][j]
                cur = nxt
            law = {}
            for (c, i), p in cur.items():
                law[c] = law.get(c, 0) + p
            base = law[(N, 0, 0, 0)]
            for m in range(1, N):
                total += 1
                if law[(m, N - m, 0, 0)] / base != S_ab(m, N - m, u):
                    bad += 1
    check('P_N(m e_i + (N-m) e_j) / P_N(N e_i) = S_{m,N-m}(u), u = ah/(1-qh)', bad == 0, f'{total} exact cases, {bad} mismatches, N = 2..9')


def check_local_law():
    print('\nTheorem 4.4 and Lemma 4.5: the local law and the lattice', flush=True)
    QR = random_gen(7)
    mu = np.ones(4) / 4
    worst40 = 0.0
    worstAB = 0.0
    for F, alphas in [([0, 1], [None, [0.3, 0.7], [0.8, 0.2]]), ([0, 1, 2], [None, [0.2, 0.5, 0.3], [0.6, 0.25, 0.15]]), ([0, 1, 2, 3], [None])]:
        A, q, m = face(QR, F, mu)
        k = len(F)
        rf = RunFace(A, q, m, mmax={2: 300, 3: 110, 4: 40}[k])
        for al in alphas:
            c = consts_A(A, q, m, al)
            alv = c['alpha'] if al is None else np.array(al)
            T = 40.0
            K = int(48 + 9 * sqrt(T)) if k < 4 else 96
            lf = torus_logf(A, q, m, alv, T, K)
            pred = (k - 1) / 2 * log(T) + log(c['K']) - T * c['I']
            worst40 = max(worst40, abs(math.expm1(lf - pred)))
            T2 = 10.0 if k == 4 else 40.0
            lfA = rf.logf(alv, T2)
            lfB = torus_logf(A, q, m, alv, T2, K)
            worstAB = max(worstAB, abs(lfA - lfB))
    check('Theorem 4.4: local law accurate to 1% at T = 40 (faces with 2, 3, 4 states)', worst40 < 0.01,
          f'max |f_T / prediction - 1| = {worst40:.4f}')
    check('f_T by the run sum = f_T by the torus', worstAB < 1e-10, f'max |log difference| = {worstAB:.1e}')
    # Lemma 4.5
    A, q, m = face(QR, [0, 1, 2], mu)
    c = consts_A(A, q, m)
    rf = RunFace(A, q, m, mmax=120)
    T, N = 10.0, 10 ** 6
    n = np.floor(N * c['alpha']).astype(int)
    n[1] += N - n.sum()
    rA = math.exp(rf.logP(n, T / N) - (rf.logf(n / N, T) - 2 * log(N)))
    rB = math.exp(torus_logP_conv(A, q, m, n, T / N) - (torus_logf(A, q, m, n / N, T, 96) - 2 * log(N)))
    check('Lemma 4.5: P_N(n) / (N^-2 f_T(n/N)) = 1 - 2.7e-5 at T = 10, N = 10^6', abs((1 - rA) - 2.7e-5) < 0.05e-5 and abs(rA - rB) < 1e-9,
          f'A {rA:.12f}, B {rB:.12f}')


def arc_max(N, h, method, rfarc=None):
    """log of the face maximum of the 3-arc of the 4-cycle (symmetric compositions (a, N-2a, a))."""
    A3 = np.array([[0, 1, 0], [1, 0, 1], [0, 1, 0]], float)
    if method == 'A':
        f = lambda a: -rfarc.logP([a, N - 2 * a, a], h)
    else:
        f = lambda a: -torus_logP(A3, [2.0] * 3, [0.25] * 3, [a, N - 2 * a, a], h, M=160)
    res = minimize_scalar(f, bounds=(N * 0.1, N * 0.4), method='bounded', options=dict(xatol=1e-7 * N))
    return -res.fun, res.x


def check_crossing():
    print('\nTheorem 4.7 and Section 5: the crossing of a vertex and the 3-arc on the 4-cycle', flush=True)
    rfarc = RunFace([[0, 1, 0], [1, 0, 1], [0, 1, 0]], [2, 2, 2], [.25] * 3, mmax=110)
    K = log((4 + 3 * sqrt(2)) / pi)
    vertex = lambda N, h: log(0.25) + (N - 1) * math.log1p(-2 * h)
    for e in (6, 14):
        N = 10 ** e
        L = log(N)
        gA = lambda T: arc_max(N, T / N, 'A', rfarc)[0] - vertex(N, T / N)
        TA = brentq(gA, 0.8 * L, 3.0 * L, xtol=1e-11, rtol=1e-14)
        # method B: one Newton step from T_A (the difference has slope about sqrt 2)
        gB = lambda T: arc_max(N, T / N, 'B')[0] - vertex(N, T / N)
        d = 1e-4
        g0, g1 = gB(TA), gB(TA + d)
        TB = TA - g0 * d / (g1 - g0)
        Kh = {'A': 2 * L - log(TA) - sqrt(2) * TA, 'B': 2 * L - log(TB) - sqrt(2) * TB}
        Troot = brentq(lambda T: sqrt(2) * T + log(T) - (2 * L - K), 1, 5 * L)
        Texp = sqrt(2) * (L - 0.5 * log(L) - 0.5 * log(sqrt(2)) - 0.5 * K)
        if e == 6:
            agree('crossing at N = 10^6 (ledger value 16.8676570)', '16.8676570', {'A': TA, 'B': TB})
            continue
        agree('T_N at N = 10^14', '42.2633', {'A': TA, 'B': TB})
        agree('Delta L - (Delta/2) log T_N - delta T_N at N = 10^14', '0.959070', Kh)
        check('the root of the implicit equation is within 0.004 of T_N', abs(Troot - TA) < 0.004, f'root {Troot:.5f}, |difference| {abs(Troot - TA):.5f}')
        agree('the explicit form gives', '42.2059', {'explicit': Texp})
        agree('T_N (Khat - log(K_F/K_G)) at N = 10^14', '-0.23335', {k: (TA if k == 'A' else TB) * (v - K) for k, v in Kh.items()})
        agree('c_arc3 - c_vertex = 5 sqrt2/4 - 2', '-0.2322', {'closed': 5 * sqrt(2) / 4 - 2})


def check_threecycle(full):
    print('\nProposition 4.13: the directed 3-cycle', flush=True)

    def gen(b):
        Q = np.array([[0, b, 0], [0, 0, 1.0], [1.0, 0, 0]], float)
        np.fill_diagonal(Q, -Q.sum(1))
        return Q
    mu = np.array([1.0, 0, 0])
    worst = 0.0
    for b in (3.0, 4.0, 5.0, 10.0):
        A, q, m = face(gen(b), [0, 1, 2], mu)
        cA = consts_A(A, q, m)
        cB = MPFace(A, q, m).data()
        s = 1 + 2 * b
        Kc = s ** 2 / (2 * sqrt(3) * pi * b)
        dH = s ** 4 / (3 * b * b)
        worst = max(worst, abs(cA['K'] / Kc - 1), abs(float(cB['K']) / Kc - 1), np.abs(cA['alpha'] - np.array([1, b, b]) / s).max(),
                    abs(1 / cA['detS'] / dH - 1), abs(1 / float(cB['detS']) / dH - 1))
    check('alpha* = (1,b,b)/(1+2b), det Hess I = (1+2b)^4/(3b^2), K_123 = (1+2b)^2/(2 sqrt3 pi b)', worst < 1e-10,
          f'max error {worst:.1e}, b = 3, 4, 5, 10')
    b = 3.0
    logM1 = lambda N, T: (N - 1) * math.log1p(-b * T / N)
    logM12 = lambda N, T: log(b * T / N) + (N - 2) * math.log1p(-T / N)
    for e, printed in ((6, '5.505516014619'), (12, '12.022801910364')):
        N = 10 ** e
        L = log(N)
        TA = brentq(lambda T: logM12(N, T) - logM1(N, T), 0.5, L, xtol=1e-14, rtol=1e-15)
        with mp.workdps(40):
            Nm = mp.mpf(N)
            TB = mp.findroot(lambda T: mp.log(b * T / Nm) + (Nm - 2) * mp.log1p(-T / Nm) - (Nm - 1) * mp.log1p(-b * T / Nm), TA)
        res = (b - 1) * TA + log(TA) - (L - log(b))
        check(f'first crossing at N = 10^{e}: (b-1)T + log T = L - log b + O(T^2/N)', abs(float(TB) - TA) < 1e-9 and abs(res) < 5 * TA * TA / N,
              f'T = {TA:.12f} (40 digits {mp.nstr(TB, 13)}), residual {res:+.3e}, 5T^2/N = {5 * TA * TA / N:.1e}')
    # the second crossing
    A, q, m = face(gen(b), [0, 1, 2], mu)
    c = consts_A(A, q, m)
    lim = log(2 * sqrt(3) * pi * b * b / (1 + 2 * b) ** 2)
    agree('limit log(2 sqrt3 pi b^2/(1+2b)^2) at b = 3', '0.692587', {'closed': lim, 'log b - log K_123': log(b) - log(c['K'])})
    rf = RunFace(A, q, m, mmax=110)

    def logM123(N, T, method):
        h = T / N
        if method == 'A':
            f = lambda x: -rf.logP([x[0] * N, x[1] * N, (1 - x[0] - x[1]) * N], h)
        else:
            f = lambda x: -torus_logP(A, q, m, [x[0] * N, x[1] * N, (1 - x[0] - x[1]) * N], h, M=128)
        r = minimize(f, c['alpha'][:2], method='Nelder-Mead', options=dict(xatol=1e-11, fatol=1e-15, maxiter=8000))
        return -r.fun
    for e, printed in ((6, '0.697542'), (8, '0.696432')):
        if e == 8 and not full:
            continue
        N = 10 ** e
        L = log(N)
        TA = brentq(lambda T: logM12(N, T) - logM123(N, T, 'A'), L - 1.5, L + 3.0, xtol=1e-9)
        d = 1e-4
        g0 = logM12(N, TA) - logM123(N, TA, 'B')
        g1 = logM12(N, TA + d) - logM123(N, TA + d, 'B')
        TB = TA - g0 * d / (g1 - g0)
        agree(f'second crossing at N = 10^{e}: T - L (ledger value)', printed, {'A': TA - L, 'B': TB - L},
              f'; T - L - limit = {TA - L - lim:+.6f}')
    # exact dynamic program at N = 300: the 3 successive modes
    N = 300

    def law(h):
        P = np.eye(3) + h * gen(b)
        D = np.zeros((3, N + 1, N + 1))
        D[0, 1, 0] = 1.0
        for _ in range(N - 1):
            E = np.zeros_like(D)
            to0 = P[0, 0] * D[0] + P[2, 0] * D[2]
            to1 = P[0, 1] * D[0] + P[1, 1] * D[1]
            to2 = P[1, 2] * D[1] + P[2, 2] * D[2]
            E[0, 1:, :] = to0[:-1, :]
            E[1, :, 1:] = to1[:, :-1]
            E[2] = to2
            D = E
        return D.sum(0)
    modes = []
    for T in (1.5, 3.5, 10.0):
        Pm = law(T / N)
        i, j = np.unravel_index(np.argmax(Pm), Pm.shape)
        modesA = (int(i), int(j), N - int(i) - int(j))
        # method B: the 3 face maxima, the full one by a lattice search with the run sum
        h = T / N
        v1 = logM1(N, T)
        v12 = logM12(N, T)
        x0 = minimize(lambda x: -rf.logP([x[0] * N, x[1] * N, (1 - x[0] - x[1]) * N], h), c['alpha'][:2], method='Nelder-Mead').x
        a0, b0 = int(round(x0[0] * N)), int(round(x0[1] * N))
        best = max(((rf.logP([a0 + i, b0 + j, N - a0 - b0 - i - j], h), (a0 + i, b0 + j, N - a0 - b0 - i - j))
                    for i in range(-3, 4) for j in range(-3, 4)))
        cands = [(v1, (N, 0, 0)), (v12, (1, N - 1, 0)), best]
        modesB = max(cands)[1]
        modes.append((modesA, modesB))
    want = [(300, 0, 0), (1, 299, 0), (44, 135, 121)]
    check('exact dynamic program at N = 300: modes at T = 1.5, 3.5, 10', all(a == b == w for (a, b), w in zip(modes, want)),
          f'DP {[a for a, _ in modes]}, face maxima {[b for _, b in modes]}')


def wick_c_euler(A, mu, alpha, rho):
    """c(alpha*) of Proposition 4.14 (the next Laplace term) with z-derivatives (Euler operators), exact in sympy."""
    k = len(alpha)
    d = k - 1
    zs = sp.symbols(f'z1:{k}')
    Ap = sp.Matrix(d, d, lambda i, j: A[i + 1][j + 1])
    a1 = sp.Matrix(1, d, lambda _, j: A[0][j + 1])
    b1 = sp.Matrix(d, 1, lambda i, _: A[i + 1][0])
    X = (sp.diag(*zs) - Ap).inv()
    g = sp.together((a1 * X * b1)[0])
    u = mu[0] + (sp.Matrix(1, d, lambda _, j: mu[j + 1]) * X * b1)[0]
    v = 1 + (a1 * X * sp.ones(d, 1))[0]
    amp = sp.together(u * v * sp.prod(zs))
    Psi = alpha[0] * g + sum(alpha[j + 1] * zs[j] for j in range(d))
    at = {zs[j]: rho[j + 1] for j in range(d)}

    def table(Fx, order):
        T = {(): Fx}
        for o in range(1, order + 1):
            for idx in itertools.combinations_with_replacement(range(d), o):
                T[idx] = zs[idx[-1]] * sp.diff(T[idx[:-1]], zs[idx[-1]])
        return {kk: sp.radsimp(sp.simplify(vv.subs(at))) * sp.I ** len(kk) for kk, vv in T.items()}
    P = table(Psi, 4)
    a = table(amp, 2)
    return _wick(P, a, d)


def wick_c_phi(A, mu, alpha, rho):
    """The same coefficient with direct angle derivatives (a second implementation)."""
    k = len(alpha)
    d = k - 1
    ph = sp.symbols(f'p1:{k}', real=True)
    z = [rho[j + 1] * sp.exp(sp.I * ph[j]) for j in range(d)]
    Ap = sp.Matrix(d, d, lambda i, j: A[i + 1][j + 1])
    a1 = sp.Matrix(1, d, lambda _, j: A[0][j + 1])
    b1 = sp.Matrix(d, 1, lambda i, _: A[i + 1][0])
    X = (sp.diag(*z) - Ap).inv()
    g = (a1 * X * b1)[0]
    R = (mu[0] + (sp.Matrix(1, d, lambda _, j: mu[j + 1]) * X * b1)[0]) * (1 + (a1 * X * sp.ones(d, 1))[0])
    Psi = alpha[0] * g + sum(alpha[j + 1] * z[j] for j in range(d))
    amp = R * sp.prod(z)
    at0 = {p: 0 for p in ph}

    def D(expr, idx):
        e = expr
        for i in idx:
            e = sp.diff(e, ph[i])
        return sp.simplify(e.subs(at0))
    P = {(): Psi.subs(at0)}
    for o in range(1, 5):
        for idx in itertools.combinations_with_replacement(range(d), o):
            P[idx] = D(Psi, idx)
    a = {(): sp.simplify(amp.subs(at0))}
    for o in range(1, 3):
        for idx in itertools.combinations_with_replacement(range(d), o):
            a[idx] = D(amp, idx)
    return _wick(P, a, d)


def _wick(Ptab, atab, d):
    Pd = lambda *ix: Ptab[tuple(sorted(ix))]
    ad = lambda *ix: atab[tuple(sorted(ix))]
    assert all(abs(complex(sp.N(Pd(j)))) < 1e-20 for j in range(d)), 'not a critical point'
    H = sp.Matrix(d, d, lambda i, j: -Pd(i, j))
    Hi = sp.simplify(H.inv())
    R = range(d)
    t1 = sum(ad(i, j) * Hi[i, j] for i in R for j in R) / 2
    t2 = sum(ad(i) * Pd(j, kk, l) * Hi[i, j] * Hi[kk, l] for i in R for j in R for kk in R for l in R) / 2
    t3 = sum(Pd(i, j, kk, l) * Hi[i, j] * Hi[kk, l] for i in R for j in R for kk in R for l in R) / 8
    t4 = t5 = 0
    for i, j, kk, l, m, n in itertools.product(R, repeat=6):
        pp = Pd(i, j, kk) * Pd(l, m, n)
        t4 += pp * Hi[i, l] * Hi[j, m] * Hi[kk, n]
        t5 += pp * Hi[i, j] * Hi[kk, l] * Hi[m, n]
    return sp.radsimp(sp.simplify((t1 + t2) / ad() + t3 + t4 / 12 + t5 / 8))


def gamma_term(adj, q, mu, astar):
    """(1/2) gamma^T Sigma gamma from the reversible closed form of C_F(alpha) (nu = 1)."""
    k = len(q)
    xs = sp.symbols(f'x1:{k}', positive=True)
    al = [1 - sum(xs)] + list(xs)
    sq = [sp.sqrt(t) for t in al]
    c = [[sq[i] * sq[j] * adj[i][j] for j in range(k)] for i in range(k)]
    Lap = sp.Matrix(k, k, lambda i, j: (sum(c[i][l] for l in range(k) if l != i) if i == j else -c[i][j]))
    tau = Lap[1:, 1:].det()
    C = sum(mu[i] * sq[i] for i in range(k)) * sum(sq) * (4 * sp.pi) ** sp.Rational(-(k - 1), 2) * sp.sqrt(tau) / sp.prod(al)
    Ifun = sum(q[i] * al[i] for i in range(k)) - sum(c[i][j] for i in range(k) for j in range(k) if i != j)
    pt = {xs[j]: astar[j + 1] for j in range(k - 1)}
    gam = sp.Matrix([sp.diff(sp.log(C), x) for x in xs]).subs(pt)
    HI = sp.Matrix(k - 1, k - 1, lambda i, j: sp.diff(Ifun, xs[i], xs[j])).subs(pt)
    return sp.radsimp(sp.simplify((gam.T * HI.inv() * gam)[0] / 2))


def check_third_order(full):
    print('\nProposition 4.14 and Section 5: the next-order coefficients c_F (exact)', flush=True)
    R = sp.Rational
    s2 = sp.sqrt(2)
    q4 = R(1, 4)
    cases = [('4-cycle pair', [[0, 1], [1, 0]], [q4] * 2, [R(1, 2)] * 2, [1, 1], None, R(-1, 8)),
             ('K_3 full face', [[0, 1, 1], [1, 0, 1], [1, 1, 0]], [R(1, 3)] * 3, [R(1, 3)] * 3, [2, 2, 2], None, R(-1, 4)),
             ('K_4 full face', [[0 if i == j else 1 for j in range(4)] for i in range(4)], [q4] * 4, [q4] * 4, [3] * 4, None, R(-3, 8)),
             ('4-cycle full', [[0, 1, 0, 1], [1, 0, 1, 0], [0, 1, 0, 1], [1, 0, 1, 0]], [q4] * 4, [q4] * 4, [2] * 4, 'rev', R(-9, 16)),
             ('4-cycle 3-arc', [[0, 1, 0], [1, 0, 1], [0, 1, 0]], [q4] * 3, [q4, R(1, 2), q4], [s2] * 3, 'rev', 5 * s2 / 4 - 2)]
    for name, A, mu, al, rho, rev, want in cases:
        cE = wick_c_euler(A, mu, al, rho)
        cP = wick_c_phi(A, mu, al, rho)
        g = gamma_term(A, [2] * len(al), mu, al) if rev else 0
        vE = sp.radsimp(sp.simplify(cE + g))
        vP = sp.radsimp(sp.simplify(cP + g))
        check(f'c_F for the {name}', sp.simplify(vE - want) == 0 and sp.simplify(vP - want) == 0,
              f'Euler form {vE}, angle form {vP}, stated {want}')
    agree('c_arc3 decimal', '-0.232233', {'exact': float(5 * s2 / 4 - 2)})
    check('pair-to-cycle remainder tends to -9/16 + 1/8 = -7/16', R(-9, 16) + R(1, 8) == R(-7, 16), 'exact')
    # the same values from the continuum, by Richardson extrapolation of T R_F(T)
    print('  continuum check: T [log max f_T - (k-1)/2 log T - log K_F + T lambda_F], Richardson in T', flush=True)
    runs = [('pair', [[0, 1], [1, 0]], [2, 2], [.25, .25], None, -0.125),
            ('3-arc', [[0, 1, 0], [1, 0, 1], [0, 1, 0]], [2, 2, 2], [.25] * 3, lambda a: np.array([a, 1 - 2 * a, a]), 5 * sqrt(2) / 4 - 2)]
    if full:
        runs.append(('4-cycle full', [[0, 1, 0, 1], [1, 0, 1, 0], [0, 1, 0, 1], [1, 0, 1, 0]], [2] * 4, [.25] * 4, None, -0.5625))
    for name, A, q, mu, sym, want in runs:
        A = np.asarray(A, float)
        q = np.asarray(q, float)
        mu = np.asarray(mu, float)
        k = len(q)
        c = consts_A(A, q, mu)
        ys = []
        Ts = [25, 50, 100, 200]
        for T in Ts:
            Kq = {2: 64 + 4 * int(6 * sqrt(T)), 3: 48 + int(9 * sqrt(T)), 4: 40 + int(7 * sqrt(T))}[k]
            if sym is None:
                lf = torus_logf(A, q, mu, c['alpha'], T, Kq)
            else:
                r = minimize_scalar(lambda x: -torus_logf(A, q, mu, sym(x), T, Kq), bounds=(c['alpha'][0] - 0.08, c['alpha'][0] + 0.08),
                                    method='bounded', options=dict(xatol=1e-10))
                lf = -r.fun
            ys.append(T * (lf - ((k - 1) / 2 * log(T) + log(c['K']) - T * c['lam'])))
        ys = np.array(ys)
        r1 = 2 * ys[1:] - ys[:-1]
        r2 = (4 * r1[1:] - r1[:-1]) / 3
        check(f'continuum c_F for the {name}', abs(r2[-1] - want) < 2e-5, f'Richardson values {np.round(r2, 6)}, exact {want:.6f}')


def check_K3_window():
    print('\nCorollary 5.2: the edge window on K_3', flush=True)
    t_ve = 0.5 * log(pi / 8)
    Kfull = 3 ** 2.5 / (4 * pi)
    t_ef = 0.5 * log(2 / pi) - log(Kfull)
    # numeric lines from the constants of the 3 face types with mu = (1/2, 1/2, 0)
    Q = complete_Q(3)
    mu = np.array([0.5, 0.5, 0.0])
    Kv = mu[0]
    Ke = consts_A(*face(Q, [0, 1], mu))['K']
    Kf = consts_A(*face(Q, [0, 1, 2], mu))['K']
    tve_n = log(Ke / Kv)                     # log Kv - 2t = log Ke - t
    tef_n = log(Ke / Kf)                     # log Ke - t = log Kf
    agree('window left end (1/2) log(pi/8)', '-0.4673558', {'closed': t_ve, 'numeric K': -tve_n})
    agree('window right end', '-0.4412978', {'closed': t_ef, 'numeric K': tef_n})
    agree('window width', '0.0260580', {'closed': t_ef - t_ve, 'numeric K': tef_n + tve_n})
    agree('criterion ratio 3^(5/2)/16', '0.97428', {'closed': 3 ** 2.5 / 16})
    agree('criterion ratio, shorter form', '0.9743', {'closed': 3 ** 2.5 / 16})
    agree('uniform start: 3^(5/2)/8 * 1/3', '0.6495', {'closed': 3 ** 2.5 / 24})
    check('uniform start: (2/3)^2 < 0.6495, so no edge window', 4 / 9 < 3 ** 2.5 / 24, f'{4 / 9:.4f} < {3 ** 2.5 / 24:.4f}')
    check('mu = (1/2,1/2,0) satisfies the criterion', 1.0 > 3 ** 2.5 / 8 * 0.5, f'1 > {3 ** 2.5 / 16:.5f}')
    # exact face maxima at N = 10^20 (and 10^16, 10^18 with --full)
    e01 = RunFace([[0, 1], [1, 0]], [2, 2], [0.5, 0.5], mmax=300)
    fullA = RunFace(np.ones((3, 3)) - np.eye(3), [2, 2, 2], [0.5, 0.5, 0.0], mmax=120)
    A3 = np.ones((3, 3)) - np.eye(3)

    def h_of(N, t):
        L = log(N)
        u = (L - 0.5 * log(L) + t) / N
        return u / (1 + 2 * u)

    def vertex(N, h):
        return log(0.5) + (N - 1) * math.log1p(-2 * h)

    def edge(N, h, method):
        n = [N / 2, N / 2]
        if method == 'A':
            return e01.logP(n, h)
        return torus_logP([[0, 1], [1, 0]], [2.0, 2.0], [0.5, 0.5], n, h, M=256)

    def fullmax(N, h, method):
        if method == 'A':
            f = lambda a: -fullA.logP([a, a, N - 2 * a], h)
        else:
            f = lambda a: -torus_logP(A3, [2.0] * 3, [0.5, 0.5, 0.0], [a, a, N - 2 * a], h, M=160)
        return -minimize_scalar(f, bounds=(0.25 * N, 0.45 * N), method='bounded', options=dict(xatol=1e-8 * N)).fun

    def that_ve(N):
        L = log(N)
        f = lambda t: (L - 0.5 * log(L) + t) + 0.5 * log(L - 0.5 * log(L) + t) - (L + 0.5 * log(pi / 8) + 1 / (8 * (L - 0.5 * log(L) + t)))
        return brentq(f, -3, 2, xtol=1e-14)
    # the ends of the window at finite N (the data of fig_window, which Paper C no longer includes); every N is cheap, so all run by default
    printed = {6: ('-0.390915', '-0.369274', None), 8: ('-0.406371', '-0.383638', None), 10: ('-0.416276', '-0.392833', None),
               12: ('-0.423230', '-0.399323', None), 14: ('-0.428404', '-0.404171', None), 16: ('-0.432415', '-0.407943', '0.02447'),
               18: ('-0.435624', '-0.410967', '0.02466'), 20: ('-0.43825', '-0.41345', '0.02480')}
    for e, (pl, pr, pw) in printed.items():
        N = 10 ** e
        res = {}
        for mth in ('A', 'B'):
            tve = brentq(lambda t: edge(N, h_of(N, t), mth) - vertex(N, h_of(N, t)), -1, 0, xtol=1e-10)
            tef = brentq(lambda t: fullmax(N, h_of(N, t), mth) - edge(N, h_of(N, t), mth), -1, 0, xtol=1e-9)
            res[mth] = (tve, tef)
        agree(f'N = 10^{e}: left end of the window', pl, {m: v[0] for m, v in res.items()})
        agree(f'N = 10^{e}: right end of the window', pr, {m: v[1] for m, v in res.items()})
        if pw is None:
            continue
        agree(f'N = 10^{e}: width', pw, {m: v[1] - v[0] for m, v in res.items()})
        th = that_ve(N)
        diff = res['A'][0] - th
        bound = 2e-5 if e == 20 else 3e-5
        check(f'N = 10^{e}: the second-order equation gives the left end to {bound:.0e}', abs(diff) < bound,
              f'root {th:.6f}, difference {diff:+.2e}')


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--full', action='store_true', help='also run the larger cells')
    args = parser.parse_args()
    t0 = time.time()
    for step in (check_engines, check_constants, check_pair_identity, check_local_law, check_crossing,
                 lambda: check_threecycle(args.full), lambda: check_third_order(args.full), check_K3_window):
        t1 = time.time()
        step()
        print(f'  ({time.time() - t1:.0f} s)', flush=True)
    print(f'\nverify_second_order: {len(FAILS)} failures, {time.time() - t0:.0f} s', flush=True)
    if FAILS:
        print('failed: ' + '; '.join(FAILS))
        sys.exit(1)


if __name__ == '__main__':
    main()
