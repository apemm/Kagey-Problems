"""Checks for the rate on a face written through flows (Proposition `prop:flows`).

For an irreducible face F and alpha in the open simplex, the rate is
   I_F(alpha) = sup_psi  sum_i alpha_i q_i - sum_{i != j} alpha_i q_ij exp(psi_j - psi_i).
With a_ij = alpha_i q_ij and the flow f_ij = a_ij exp(psi_j - psi_i) at the maximizer we check
  A. f is balanced, f_ij f_ji = a_ij a_ji on every pair, I_F = sum alpha_i q_i - sum f_ij,
     and f has the product of a around every directed cycle;
  B. sum_i alpha_i q_i^out + sum Phi(J_ij, a_ij) is at least I_F for balanced flows J near and
     far from f, with equality at f, where Phi(J, a) = J log(J/a) - J + a;
  C. I_F <= R (the reversible formula), with gap sum over pairs (sqrt f_ij - sqrt f_ji)^2,
     and the gap is 0 for reversible faces;
  D. on a two-way cycle, the one equation for the net flow c;
  E. on a one-way cycle, the form with the geometric mean;
  F. the Perron root of Q_F is at least that of its geometric symmetrization;
  G. the numbers of the worked example in the paper.
Run: python -B verify_rate_flows.py     (a few seconds)
"""
import itertools
import math

import numpy as np
from scipy.optimize import brentq, minimize

rng = np.random.default_rng(131)
checks = 0


def ok(cond, what):
    global checks
    assert cond, what
    checks += 1


def rate(q, qtot, alpha):
    """I_F(alpha), the maximizing psi and the flow f. q has zero diagonal, qtot = exit rates."""
    k = len(alpha)
    a = alpha[:, None] * q

    def neg(psi):
        e = np.exp(psi[None, :] - psi[:, None])
        f = a * e
        return f.sum(), f.sum(1) - f.sum(0)          # value and gradient of sum f in psi (negated)

    def fun(x):
        psi = np.concatenate(([0.0], x))
        v, g = neg(psi)
        return v, -g[1:]

    res = minimize(fun, np.zeros(k - 1), jac=True, method="BFGS", options={"gtol": 1e-13, "maxiter": 5000})
    psi = np.concatenate(([0.0], res.x))
    for _ in range(50):                               # polish with Newton steps
        f = a * np.exp(psi[None, :] - psi[:, None])
        g = (f.sum(0) - f.sum(1))[1:]
        H = -(f + f.T)
        H[np.diag_indices(k)] = f.sum(0) + f.sum(1)
        step = np.linalg.solve(H[1:, 1:], -g)
        psi[1:] += step
        if abs(step).max() < 1e-15:
            break
    f = a * np.exp(psi[None, :] - psi[:, None])
    return float(alpha @ qtot - f.sum()), psi, f


def phi(J, a):
    m = a > 0
    out = np.zeros_like(a)
    Jm, am = J[m], a[m]
    out[m] = np.where(Jm > 0, Jm * np.log(np.where(Jm > 0, Jm, 1.0) / am), 0.0) - Jm + am
    return out.sum()


def random_face(k, kind):
    q = np.zeros((k, k))
    if kind == "dense":
        q = rng.uniform(0.2, 3.0, (k, k))
    elif kind == "sparse":                           # a one-way cycle plus some extra edges
        for i in range(k):
            q[i, (i + 1) % k] = rng.uniform(0.2, 3.0)
        for i, j in itertools.permutations(range(k), 2):
            if q[i, j] == 0 and rng.random() < 0.35:
                q[i, j] = rng.uniform(0.2, 3.0)
    elif kind == "reversible":
        nu = rng.uniform(0.5, 2.0, k)
        c = rng.uniform(0.2, 3.0, (k, k))
        c = (c + c.T) * (rng.random((k, k)) < 0.7)
        c = np.triu(c, 1)
        for i in range(k - 1):
            c[i, i + 1] = c[i, i + 1] or 1.0         # keep it connected
        c = c + c.T
        q = c / nu[:, None]
    np.fill_diagonal(q, 0.0)
    out = rng.uniform(0.0, 1.5, k) * (rng.random(k) < 0.6)
    return q, q.sum(1) + out


def cycles(k):
    for r in range(2, k + 1):
        for comb in itertools.combinations(range(k), r):
            for perm in itertools.permutations(comb[1:]):
                yield (comb[0],) + perm


def main():
    # ---------- A, B, C, F on random faces
    for kind in ("dense", "sparse", "reversible"):
        for k in (2, 3, 4, 5):
            for _ in range(40):
                q, qtot = random_face(k, kind)
                alpha = rng.dirichlet(np.ones(k) * 2)
                a = alpha[:, None] * q
                I, psi, f = rate(q, qtot, alpha)
                tag = "%s k=%d" % (kind, k)
                ok(abs(f.sum(0) - f.sum(1)).max() < 1e-10, "balanced " + tag)
                ok(abs(f * f.T - a * a.T).max() < 1e-10, "pair products " + tag)
                for cyc in cycles(k):
                    pf = math.prod(f[cyc[i], cyc[(i + 1) % len(cyc)]] for i in range(len(cyc)))
                    pa = math.prod(a[cyc[i], cyc[(i + 1) % len(cyc)]] for i in range(len(cyc)))
                    ok(abs(pf - pa) <= 1e-9 * max(pa, 1e-30) + 1e-14, "cycle products " + tag)
                # the supremum really is I: random psi give smaller values
                for _ in range(20):
                    p2 = psi + rng.normal(0, 0.5, k)
                    v = alpha @ qtot - (a * np.exp(p2[None, :] - p2[:, None])).sum()
                    ok(v <= I + 1e-10, "sup " + tag)
                base = alpha @ (qtot - q.sum(1))
                ok(abs(base + phi(f, a) - I) < 1e-9, "flow form at f " + tag)
                # other balanced flows: stationary flows of random generators with the same graph
                for _ in range(20):
                    g = q * rng.uniform(0.2, 3.0, (k, k))
                    G = g - np.diag(g.sum(1))
                    w, vl = np.linalg.eig(G.T)
                    pi = np.real(vl[:, np.argmin(abs(w))])
                    pi = pi / pi.sum()
                    J = pi[:, None] * g * rng.uniform(0.1, 3.0)
                    ok(abs(J.sum(0) - J.sum(1)).max() < 1e-9, "test flow balanced")
                    ok(base + phi(J, a) >= I - 1e-10, "flow form lower bound " + tag)
                    Jn = f + 1e-3 * (J - f)          # near f
                    ok(base + phi(Jn, a) >= I - 1e-12, "flow form near f " + tag)
                R = alpha @ qtot - np.sqrt(a * a.T).sum()
                gap = sum((math.sqrt(f[i, j]) - math.sqrt(f[j, i])) ** 2 for i in range(k) for j in range(i))
                ok(abs(R - I - gap) < 1e-9, "gap " + tag)
                ok(I <= R + 1e-10, "I <= R " + tag)
                if kind == "reversible":
                    ok(gap < 1e-9, "reversible gap 0 " + tag)
                elif k >= 3:
                    ok(gap > 1e-9, "non-reversible gap > 0 " + tag)
                # F: Perron roots
                QF = q - np.diag(qtot)
                S = np.sqrt(q * q.T) - np.diag(qtot)
                ok(max(np.linalg.eigvals(QF).real) >= max(np.linalg.eigvalsh(S)) - 1e-10, "Perron " + tag)

    # ---------- D: two-way cycles
    for k in (3, 4, 5, 7):
        for _ in range(40):
            p, m = rng.uniform(0.2, 3.0, k), rng.uniform(0.2, 3.0, k)
            q = np.zeros((k, k))
            for i in range(k):
                q[i, (i + 1) % k] = p[i]
                q[(i + 1) % k, i] = m[i]
            qtot = q.sum(1) + rng.uniform(0, 1, k)
            alpha = rng.dirichlet(np.ones(k) * 2)
            g = np.array([math.sqrt(alpha[i] * alpha[(i + 1) % k] * p[i] * m[i]) for i in range(k)])
            target = 0.5 * math.log(np.prod(p) / np.prod(m))
            c = brentq(lambda c: np.arcsinh(c / (2 * g)).sum() - target, -1e3, 1e3, xtol=1e-15, rtol=1e-15)
            I, psi, f = rate(q, qtot, alpha)
            ok(abs(I - (alpha @ qtot - np.sqrt(c * c + 4 * g * g).sum())) < 1e-9, "cycle formula k=%d" % k)
            for i in range(k):
                ok(abs(f[i, (i + 1) % k] - f[(i + 1) % k, i] - c) < 1e-9, "net flow k=%d" % k)
            fwd = (c + np.sqrt(c * c + 4 * g * g)) / 2
            ok(abs(np.prod(fwd) - np.prod(alpha) * np.prod(p)) < 1e-10, "forward product k=%d" % k)

    # ---------- E: one-way cycles
    for k in (2, 3, 4, 6):
        for _ in range(40):
            p = rng.uniform(0.2, 3.0, k)
            q = np.zeros((k, k))
            for i in range(k):
                q[i, (i + 1) % k] = p[i]
            if k == 2:
                continue                              # for k = 2 this is a reversible pair
            qtot = q.sum(1) + rng.uniform(0, 1, k)
            alpha = rng.dirichlet(np.ones(k) * 2)
            I, _, _ = rate(q, qtot, alpha)
            ok(abs(I - (alpha @ qtot - k * np.prod(alpha * p) ** (1 / k))) < 1e-9, "one-way k=%d" % k)

    # ---------- G: the worked example, the 3-cycle with rates p forward and m backward
    p, m, k = 2.0, 1.0, 3
    q = np.zeros((3, 3))
    for i in range(3):
        q[i, (i + 1) % 3] = p
        q[(i + 1) % 3, i] = m
    qtot = q.sum(1)
    print("the cycle with k = 3, p = 2, m = 1")
    for alpha in (np.ones(3) / 3, np.array([0.5, 0.3, 0.2]), np.array([0.8, 0.1, 0.1])):
        g = np.array([math.sqrt(alpha[i] * alpha[(i + 1) % 3] * p * m) for i in range(3)])
        c = brentq(lambda c: np.arcsinh(c / (2 * g)).sum() - 1.5 * math.log(p / m), 0, 10, xtol=1e-15)
        I = p + m - np.sqrt(c * c + 4 * g * g).sum()
        I2, _, _ = rate(q, qtot, alpha)
        R = p + m - 2 * g.sum()
        ok(abs(I - I2) < 1e-10, "example")
        print("   alpha = %s: c = %.4f, I = %.4f, reversible formula R = %.4f" % (np.round(alpha, 3), c, I, R))
    ok(abs(brentq(lambda c: 3 * math.asinh(c / (2 * math.sqrt(2) / 3)) - 1.5 * math.log(2), 0, 10) - 1 / 3) < 1e-12,
       "c at the uniform law is (p - m)/k")
    # the slice of an even cycle where alpha_i alpha_{i+1} is constant
    for k in (4, 6):
        a_, b_ = 0.7 * 2 / k, 0.3 * 2 / k
        alpha = np.array([a_, b_] * (k // 2))
        q = np.zeros((k, k))
        for i in range(k):
            q[i, (i + 1) % k] = p
            q[(i + 1) % k, i] = m
        I, _, _ = rate(q, q.sum(1), alpha)
        ok(abs(I - (p + m) * (1 - k * math.sqrt(a_ * b_))) < 1e-10, "even slice k=%d" % k)
    print("verify_rate_flows.py: all %d checks passed." % checks)


if __name__ == "__main__":
    main()
