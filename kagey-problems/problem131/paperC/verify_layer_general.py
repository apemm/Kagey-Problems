"""Numerical check of Theorem `thm:L-facet` (the weighted facet chain) for facets with four states.

For a facet G of a face F = G + {i}, with c^-_j = q_ji, c^+_j = q_ij and complex z, the weights
of Section `sec:layer-setting` are
    A(z) = A_G + z offdiag(c^- c^+T),  d(z) = q_G - z c^- o c^+,
    mu^(z) = mu_G + z mu_i c^+,        e^(z) = 1 + z c^-,
and f^(z)_G(s) = e^{-<d(z), s>} sum_m W_z(m) prod_j s_j^{m_j - 1}/(m_j - 1)! is the word sum of
Lemma `lem:layer-exact`. Theorem `thm:L-facet` says that
    f^(z)_G(S beta) = S^{-(k-2)/2} C_G(beta, z) e^{-S J_G(beta, z)} (1 + eps),  |eps| <= C/S,
with J_G = <d(z), beta> - Phi_z(zeta') and C_G = (2 pi)^{-m/2} det(J)^{-1/2} b_z(zeta') prod zeta_j,
where zeta' is the complex critical point of Lemma `lem:critical` and J = Z_c grad^2 Phi_z Z_c.

Two facets with four states (so k - 2 = 3 and the power is S^{-3/2}):
  - a facet of a non-reversible face with five states, with start mass on i;
  - the path 1-2-3-4 with unequal rates and killing, whose jump chain is periodic.

  A. The word sum. It is computed exactly, without the torus, by a recursion over the words that
     carries the counts of the letters and folds in the factors s_j^{m_j-1}/(m_j-1)!. The recursion
     is checked against a direct enumeration of all words up to length 9.
  B. Lemma `lem:critical`(e). For real z >= 0 the critical point, the rate and the constant from
     the torus agree with the tilt of Q_G(z) and with the constant of Section `sec:layer-setting`
     (through Sigma_beta(z) of Definition `def:tilt`).
  C. The expansion. For z = 0, 0.08i and 0.1 e^{2 pi i/3}, the exact f^(z)_G(S beta) is divided by
     the prediction, and S |eps| is printed for S = 4, 8, 16, 32 (and 64 with --full). The products
     settle to a constant, the ratio of consecutive products tends to 1, and the cancellation in
     the word sum is small enough that double precision is not the limit. The caps on the counts
     are checked by enlarging them at the largest S.

Every check is an assertion. Nothing in the paper is deduced from these numbers.
Needs numpy. Run:  py -I verify_layer_general.py [--full]   (about two minutes, --full about ten)
"""
import argparse
import itertools
from math import pi, sqrt

import numpy as np

CHECKS = 0


def ok(cond, what):
    global CHECKS
    if not cond:
        raise AssertionError(what)
    CHECKS += 1
    print("  ok   ", what, flush=True)


# ------------------------------------------------------------------ the facet chain
def facet(Qoff, kill, mu, i):
    """Data of the facet G = F minus {i}. Qoff holds the jump rates on F, kill the extra exit rates."""
    Q = np.array(Qoff, float)
    np.fill_diagonal(Q, 0.0)
    q = Q.sum(axis=1) + np.asarray(kill, float)
    G = [j for j in range(Q.shape[0]) if j != i]
    return dict(A=Q[np.ix_(G, G)], q=q[G], cm=Q[G, i], cp=Q[i, G], muG=np.asarray(mu, float)[G],
                mui=float(mu[i]), g=len(G))


def weights(fd, z):
    A = fd['A'] + z * np.outer(fd['cm'], fd['cp'])
    np.fill_diagonal(A, 0.0)
    d = fd['q'] - z * fd['cm'] * fd['cp']
    nu = fd['muG'] + z * fd['mui'] * fd['cp']
    e = 1.0 + z * fd['cm']
    return A.astype(complex), d.astype(complex), nu.astype(complex), e.astype(complex)


# ------------------------------------------------------------------ A. the exact word sum
def word_layers(A, nu, e, s, caps, tol=1e-22):
    """Layer sums of the word sum H(s) = sum_m W(m) prod_j s_j^{m_j-1}/(m_j-1)!.

    The entry N[a][c] is the weighted sum over the words of the current length L that end in the
    letter a and have c_j letters j for j < g-1 (the last letter has L - sum c letters), with the
    factors s_j^{m_j-1}/(m_j-1)! folded in. Adding a letter j that already occurs n times
    multiplies by s_j/n. Counts above caps[j] are dropped. Returns the array of the layer sums
    over the words that contain every letter."""
    g = len(s)
    d = g - 1
    shape = tuple(c + 1 for c in caps[:d])
    idx = np.indices(shape)
    csum = idx.sum(axis=0)
    allpos = np.all(idx >= 1, axis=0)
    mlast = caps[d]
    N = np.zeros((g,) + shape, complex)
    for a in range(g):
        c = [0] * d
        if a < d:
            c[a] = 1
        N[(a,) + tuple(c)] = nu[a]
    fac_axis = []
    for a in range(d):
        n = idx[a]
        fac_axis.append(np.where(n >= 2, s[a] / np.maximum(n - 1, 1), 1.0))
    layers, best, quiet = [], 0.0, 0
    for L in range(1, sum(caps) + 1):
        last = L - csum
        valid = allpos & (last >= 1) & (last <= mlast)
        val = sum(e[a] * N[a][valid].sum() for a in range(g))
        layers.append(val)
        best = max(best, abs(val))
        quiet = quiet + 1 if abs(val) < tol * best else 0
        if quiet >= 12:
            break
        acc = np.tensordot(A.T, N, axes=1)          # acc[a] = sum_b A[b, a] N[b]
        new = np.zeros_like(N)
        for a in range(d):
            dst = [a] + [slice(None)] * d
            src = [a] + [slice(None)] * d
            dst[1 + a] = slice(1, None)
            src[1 + a] = slice(0, -1)
            new[tuple(dst)] = acc[tuple(src)]
            new[a] *= fac_axis[a]
        n = (L + 1) - csum
        fac = np.where(n >= 2, s[d] / np.maximum(n - 1, 1), 1.0)
        new[d] = acc[d] * np.where((n >= 1) & (n <= mlast), fac, 0.0)
        N = new
    return np.array(layers)


def brute_layers(A, nu, e, s, Lmax):
    """The same layer sums by enumerating every word up to length Lmax."""
    g = len(s)
    out = np.zeros(Lmax, complex)
    fact = [1.0]
    for n in range(1, Lmax + 1):
        fact.append(fact[-1] * n)
    for L in range(1, Lmax + 1):
        for w in itertools.product(range(g), repeat=L):
            if any(w[t] == w[t + 1] for t in range(L - 1)):
                continue
            m = np.bincount(w, minlength=g)
            if m.min() == 0:
                continue
            wt = nu[w[0]] * e[w[-1]]
            for t in range(L - 1):
                wt *= A[w[t], w[t + 1]]
            for j in range(g):
                wt *= s[j] ** (m[j] - 1) / fact[m[j] - 1]
            out[L - 1] += wt
    return out


# ------------------------------------------------------------------ B. the prediction
def real_tilt(A, beta, iters=200):
    """The vector r_beta and theta = A r / r of Definition def:tilt for a nonnegative A."""
    g = len(beta)
    psi = np.zeros(g)
    for _ in range(iters):
        W = beta[:, None] * A * np.exp(psi[None, :] - psi[:, None])
        grad = W.sum(axis=0) - W.sum(axis=1)
        H = np.diag(W.sum(axis=0) + W.sum(axis=1)) - W - W.T
        step = np.zeros(g)
        step[1:] = np.linalg.solve(H[1:, 1:], grad[1:])
        psi -= step
        if np.abs(step).max() < 1e-15:
            break
    r = np.exp(psi)
    return r, A @ r / r


def setting_constants(fd, beta, z):
    """Rate and constant of Section sec:layer-setting for real z >= 0, through Sigma_beta(z)."""
    A, d, nu, e = (x.real for x in weights(fd, z))
    r, th = real_tilt(A, beta)
    l = beta / r
    g = len(beta)
    R = np.diag(r)
    Qhat = np.linalg.inv(R) @ (A - np.diag(th)) @ R
    one = np.ones(g)
    Z = np.linalg.inv(np.outer(one, beta) - Qhat) - np.outer(one, beta)
    Gam = np.diag(beta) @ Z + Z.T @ np.diag(beta)
    Sig = Gam[1:, 1:]
    C = (nu @ r) * (l @ e) / ((2 * pi) ** ((g - 1) / 2) * sqrt(np.linalg.det(Sig)))
    return th, float(beta @ (d - th)), C


def torus(A, nu, e, zp):
    """g_z, its gradient and Hessian, and b_z at z' (Lemma lem:torus-complex, state 1 split off)."""
    a1, b1, Ap = A[0, 1:], A[1:, 0], A[1:, 1:]
    X = np.linalg.inv(np.diag(zp) - Ap)
    u, v = a1 @ X, X @ b1
    M = u[:, None] * X * v[None, :]
    b = (nu[0] + nu[1:] @ v) * (e[0] + u @ e[1:])
    return u @ b1, -u * v, M + M.T, b


def prediction(fd, beta, z, steps=20):
    """zeta', J_G and log C_G of Theorem thm:L-facet, continued along the segment [0, z]."""
    A0 = weights(fd, 0.0)[0].real
    _, th0 = real_tilt(A0, beta)
    zp = th0[1:].astype(complex)
    root = None
    for t in np.linspace(0.0, 1.0, steps + 1):
        A, d, nu, e = weights(fd, t * z)
        for _ in range(50):
            _, grad, hess, _ = torus(A, nu, e, zp)
            step = np.linalg.solve(beta[0] * hess, -(beta[0] * grad + beta[1:]))
            zp = zp + step
            if np.abs(step).max() < 1e-15 * np.abs(zp).max():
                break
        gval, grad, hess, b = torus(A, nu, e, zp)
        J = np.diag(zp) @ (beta[0] * hess) @ np.diag(zp)
        new = np.sqrt(np.linalg.det(J) + 0j)
        if root is not None and abs(new + root) < abs(new - root):
            new = -new
        root = new
    m = len(beta) - 1
    Phi = beta[0] * gval + beta[1:] @ zp
    return dict(zp=zp, J=J, JG=beta @ d - Phi, logC=np.log((2 * pi) ** (-m / 2) * b * np.prod(zp) / root),
                minReJ=np.linalg.eigvalsh(J.real).min(), resid=np.abs(beta[0] * grad + beta[1:]).max())


# ------------------------------------------------------------------ C. the expansion
def caps_for(fd, beta, S, z, widen=1.0):
    """Caps on the counts: theta_j s_j + 8 sqrt(theta_j s_j) + 10 for the weights at |z|."""
    _, th = real_tilt(weights(fd, abs(z))[0].real, beta)
    x = th * S * beta
    return [int(widen * (xj + 8 * sqrt(xj) + 10)) for xj in x]


def log_f(fd, beta, S, z, widen=1.0, moduli=False):
    A, d, nu, e = weights(fd, z)
    s = S * beta
    caps = caps_for(fd, beta, S, z, widen)
    H = word_layers(A, nu, e, s, caps).sum()
    out = np.log(H + 0j) - d @ s
    if moduli:
        Habs = word_layers(np.abs(A), np.abs(nu), np.abs(e), s, caps).sum().real
        return out, np.log(Habs) - np.log(abs(H))
    return out


def run_chain(name, fd, beta, Slist):
    beta = np.asarray(beta, float)
    m = fd['g'] - 1
    print(f"{name}, beta = {beta}")
    print(f"  c^- = {fd['cm']}, c^+ = {fd['cp']}, mu_G = {fd['muG']}, mu_i = {fd['mui']}")

    for z in (0.0, 0.05):
        th, JG, C = setting_constants(fd, beta, z)
        p = prediction(fd, beta, z)
        ok(np.abs(p['zp'] - th[1:]).max() < 1e-10 and abs(p['JG'] - JG) < 1e-10
           and abs(np.exp(p['logC']) / C - 1) < 1e-10,
           f"z = {z}: torus critical point = tilt of Q_G(z), J_G = {JG:.10f} and C_G = {C:.10f} "
           f"agree with Section 6.1 (Lemma lem:critical(e))")

    zs = (0.0, 0.08j, 0.1 * np.exp(2j * pi / 3))
    print(f"  S |eps| for S = {', '.join(str(int(S)) for S in Slist)}")
    for z in zs:
        p = prediction(fd, beta, z)
        prods, kappa = [], None
        for S in Slist:
            moduli = S == Slist[-1]
            res = log_f(fd, beta, S, z, moduli=moduli)
            if moduli:
                res, kappa = res
            logpred = p['logC'] - S * p['JG'] - (m / 2) * np.log(S)
            eps = np.exp(res - logpred) - 1
            prods.append(S * abs(eps))
        ratios = [prods[t + 1] / prods[t] for t in range(len(prods) - 1)]
        zs_ = f"{complex(z).real:+.4f}{complex(z).imag:+.4f}i"
        print(f"    z = {zs_}: " + "  ".join(f"{x:.5f}" for x in prods)
              + "   ratios " + "  ".join(f"{x:.4f}" for x in ratios)
              + f"   least eigenvalue of Re J = {p['minReJ']:.3f}, cancellation exponent {kappa:.2f}")
        dev = [abs(x - 1) for x in ratios]
        # e^kappa times the rounding error 1e-16 must stay far below |eps|, which is about 0.01
        ok(p['resid'] < 1e-12 and p['minReJ'] > 0.1 and kappa < 10,
           f"z = {zs_}: critical point found, Re J positive definite, cancellation e^{kappa:.2f}")
        ok(max(prods) < 2 and dev[-1] < 0.01 and all(dev[t + 1] < dev[t] for t in range(len(dev) - 1)),
           f"z = {zs_}: S |eps| settles at {prods[-1]:.4f}, last ratio {ratios[-1]:.4f}")
    S = Slist[-1]
    a = log_f(fd, beta, S, 0.0)
    b = log_f(fd, beta, S, 0.0, widen=1.4)
    ok(abs(np.exp(b - a) - 1) < 1e-13, f"S = {S:.0f}: enlarging the caps by 40 percent changes f by "
                                        f"{abs(np.exp(b - a) - 1):.1e}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--full', action='store_true', help='also S = 64')
    args = parser.parse_args()
    Slist = [4.0, 8.0, 16.0, 32.0] + ([64.0] if args.full else [])

    # a facet of a non-reversible face with five states, i = 5 (index 4)
    Q5 = [[0.0, 1.5, 0.7, 0.5, 0.8],
          [0.5, 0.0, 1.5, 0.0, 0.0],
          [0.0, 0.5, 0.0, 1.5, 1.2],
          [1.5, 0.0, 0.5, 0.0, 0.3],
          [0.5, 1.0, 0.0, 0.9, 0.0]]
    face5 = facet(Q5, np.zeros(5), [0.2, 0.1, 0.3, 0.15, 0.25], 4)
    beta5 = [0.3, 0.25, 0.2, 0.25]
    # the path 1-2-3-4 with killing 0.2, i entered from 4 and 1 and left to 1 and 3
    P = np.zeros((5, 5))
    P[0, 1], P[1, 0], P[1, 2], P[2, 1], P[2, 3], P[3, 2] = 2.0, 1.0, 1.5, 0.7, 2.2, 1.1
    P[3, 4], P[0, 4], P[4, 0], P[4, 2] = 1.3, 0.4, 1.0, 0.6
    path = facet(P, np.full(5, 0.2), [0.3, 0.15, 0.2, 0.2, 0.15], 4)
    betap = [0.3, 0.2, 0.25, 0.25]

    print("A. The recursion over the words against a direct enumeration (words up to length 9)")
    for name, fd, beta in (("face with five states", face5, beta5), ("path", path, betap)):
        for z in (0.0, 0.1 * np.exp(2j * pi / 3)):
            A, d, nu, e = weights(fd, z)
            s = 1.5 * np.asarray(beta)
            rec = word_layers(A, nu, e, s, [9] * 4, tol=0.0)[:9]
            bru = brute_layers(A, nu, e, s, 9)
            err = np.abs(rec - bru).max() / np.abs(bru).max()
            ok(err < 1e-13, f"{name}, z = {complex(z):.4f}: layer sums agree to {err:.1e}")

    print("B, C. The critical point and the expansion")
    run_chain("Facet of a non-reversible face with five states", face5, beta5, Slist)
    run_chain("The path 1-2-3-4 (periodic jump chain)", path, betap, Slist)
    print(f"verify_layer_general: all {CHECKS} checks passed")


if __name__ == "__main__":
    main()
