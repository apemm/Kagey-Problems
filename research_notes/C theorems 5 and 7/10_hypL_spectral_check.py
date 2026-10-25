"""Numerical check of the spectral route to Hypothesis L (note 10_hypL_spectral_route.md).

Run with:  py -I 10_hypL_spectral_check.py  > 10_hypL_spectral_output.txt

What it does, for four non-reversible faces (facet sizes g = 3 and g = 4):

  Part 1. Checks the exact representation (Lemma R of the note) against the word series of
          Lemma lem:layer-exact at small S, for real and complex z and for real and complex radii.
  Part 2. Solves the complex tilt theta(beta, z), forms the Doob transform P_0, and prints its
          spectrum (Perron eigenvalue 1, the other eigenvalues, the gap gamma_0) and w.
  Part 3. Checks the determinant identity det H_Phi = prod theta^2 det Sigma / <theta,beta>^2,
          i.e. that the constant of the spectral route equals the paper's constant C_G(beta, z).
  Part 4. Computes the exact f^{(z)}_G(S beta) by the representation (trapezoid rule on the torus,
          two grid sizes) and compares it with S^{-(g-1)/2} C_G(beta,z) e^{-S J_G(beta,z)} for
          S = 25 ... 400 (g = 4) and up to 800 (g = 3). Prints |eps| and S |eps|.
"""
import itertools
import math
import numpy as np

np.set_printoptions(linewidth=140, precision=6)


# ----------------------------------------------------------------------------------------------
# Faces
# ----------------------------------------------------------------------------------------------

def facet_data(Qoff, kill, i, mu):
    """Qoff: off-diagonal rates on F (k x k, zero diagonal), kill: extra killing on F,
    i: index of the removed state, mu: start on F.  Returns the facet data of the paper."""
    k = Qoff.shape[0]
    q = Qoff.sum(axis=1) + kill            # total exit rates q_j
    G = [j for j in range(k) if j != i]
    A0 = Qoff[np.ix_(G, G)].astype(complex)
    qG = q[G].astype(complex)
    cm = Qoff[G, i].astype(complex)        # c^-_j = q_{ji}
    cp = Qoff[i, G].astype(complex)        # c^+_j = q_{ij}
    return dict(A0=A0, qG=qG, cm=cm, cp=cp, muG=mu[G].astype(complex), mui=complex(mu[i]), g=len(G))


def weighted(D, z):
    """A(z), d(z), mu^(z), e^(z)."""
    R1 = np.outer(D['cm'], D['cp'])
    A = D['A0'] + z * (R1 - np.diag(np.diag(R1)))
    d = D['qG'] - z * D['cm'] * D['cp']
    mu = D['muG'] + z * D['mui'] * D['cp']
    e = np.ones(D['g'], complex) + z * D['cm']
    return A, d, mu, e


def make_faces():
    faces = []
    # (a) F = non-reversible 4-cycle 0->1->2->3->0 rate 2, reverse rate 1; facet = path {0,1,2}.
    k = 4
    Q = np.zeros((k, k))
    for a in range(k):
        Q[a, (a + 1) % k] = 2.0
        Q[a, (a - 1) % k] = 1.0
    faces.append(('F = 4-cycle (2 forward, 1 back), i = 3, facet = path of 3 states',
                  Q, np.full(k, 0.3), 3, np.full(k, 1.0 / k), np.array([0.3, 0.3, 0.4])))
    # (b) F = complete graph on 4 states, non-reversible rates; facet = K3.
    Q = np.array([[0, 1.0, 2.5, 0.7],
                  [0.4, 0, 1.2, 1.9],
                  [1.6, 0.3, 0, 0.8],
                  [2.2, 0.5, 1.1, 0]])
    faces.append(('F = K4 non-reversible, i = 3, facet = K3',
                  Q, np.array([0.2, 0.0, 0.5, 0.1]), 3, np.full(4, 0.25), np.array([0.25, 0.35, 0.40])))
    # (c) facet G = non-reversible 4-cycle on {0,1,2,3}, extra state 4 entered from 0,2, left to 1,3.
    k = 5
    Q = np.zeros((k, k))
    for a in range(4):
        Q[a, (a + 1) % 4] = 2.0
        Q[a, (a - 1) % 4] = 1.0
    Q[0, 4] = 1.5; Q[2, 4] = 0.5
    Q[4, 1] = 2.0; Q[4, 3] = 1.0
    faces.append(('G = 4-cycle (2 forward, 1 back), i = 4 entered from 0,2 and left to 1,3',
                  Q, np.full(k, 0.2), 4, np.full(k, 0.2), np.array([0.2, 0.3, 0.25, 0.25])))
    # (d) facet G = K4 with non-reversible rates, extra state 4.
    rng = np.random.default_rng(131)
    Q = rng.uniform(0.3, 2.5, size=(5, 5))
    np.fill_diagonal(Q, 0.0)
    faces.append(('G = K4 random non-reversible rates (seed 131), i = 4',
                  Q, np.full(5, 0.1), 4, np.array([0.3, 0.1, 0.2, 0.25, 0.15]),
                  np.array([0.2, 0.3, 0.15, 0.35])))
    return faces


# ----------------------------------------------------------------------------------------------
# Word series (Lemma lem:layer-exact), by dynamic programming over the letter counts
# ----------------------------------------------------------------------------------------------

def word_series(D, z, s, mmax):
    A, d, mu, e = weighted(D, z)
    g = D['g']
    shape = (g,) + (mmax + 1,) * g
    W = np.zeros(shape, complex)          # W[last, m_1..m_g]
    for j in range(g):
        idx = [0] * g; idx[j] = 1
        W[(j,) + tuple(idx)] = mu[j]
    total = 0j
    fac = [math.factorial(n) for n in range(mmax + 1)]
    allm = sorted(itertools.product(range(0, mmax + 1), repeat=g), key=sum)
    for m in allm:                       # increasing word length, so W[., m] is final here
        if min(m) >= 1:
            wt = sum(W[(j,) + m] * e[j] for j in range(g))
            term = wt
            for j in range(g):
                term *= s[j] ** (m[j] - 1) / fac[m[j] - 1]
            total += term
        for j in range(g):
            v = W[(j,) + m]
            if v == 0:
                continue
            for jp in range(g):
                if jp == j or m[jp] == mmax:
                    continue
                m2 = list(m); m2[jp] += 1
                W[(jp,) + tuple(m2)] += v * A[j, jp]
    return np.exp(-np.dot(d, s)) * total


# ----------------------------------------------------------------------------------------------
# Batched matrix exponential (Taylor with scaling and squaring)
# ----------------------------------------------------------------------------------------------

def expm_batch(X, deg=18):
    nrm = np.abs(X).sum(axis=2).max()
    sq = max(0, int(math.ceil(math.log2(max(nrm, 1e-300) / 0.25))))
    Y = X / (2.0 ** sq)
    n, g, _ = X.shape
    I = np.broadcast_to(np.eye(g, dtype=complex), X.shape)
    E = I.copy()
    term = I.copy()
    for k in range(1, deg + 1):
        term = term @ Y / k
        E = E + term
    for _ in range(sq):
        E = E @ E
    return E


# ----------------------------------------------------------------------------------------------
# The representation (Lemma R): returns  (2 pi)^{-(g-1)} int mu^T K^{g-1} e^{cK - T0} D^{-1} e prod theta e^{i psi}
# so that  f^{(z)}(s) = e^{-<d,s>} e^{T0} * value.
# ----------------------------------------------------------------------------------------------

def rep_integral(D, z, s, theta, N, T0=None, chunk=40000):
    A, d, mu, e = weighted(D, z)
    g = D['g']
    if T0 is None:
        T0 = np.dot(s, theta)
    grid1 = 2 * np.pi * np.arange(N) / N
    pts = np.array(list(itertools.product(range(N), repeat=g - 1)))
    total = 0j
    for c0 in range(0, len(pts), chunk):
        P = pts[c0:c0 + chunk]
        n = len(P)
        psi = np.zeros((n, g))
        psi[:, 1:] = grid1[P]
        Dz = theta[None, :] * np.exp(1j * psi)                  # (n, g)
        K = A[None, :, :] / Dz[:, :, None]                       # D^{-1} A
        c = (s[None, :] * Dz).sum(axis=1)                        # (n,)
        X = c[:, None, None] * K - T0 * np.eye(g)[None]
        E = expm_batch(X)
        v = (e[None, :] / Dz)[:, :, None]                        # D^{-1} e
        v = E @ v
        for _ in range(g - 1):
            v = K @ v
        val = (mu[None, None, :] @ v)[:, 0, 0] * np.prod(Dz, axis=1)
        total += val.sum()
    return total / N ** (g - 1)


# ----------------------------------------------------------------------------------------------
# The complex tilt and the constants
# ----------------------------------------------------------------------------------------------

def eig_near(M, target):
    w, V = np.linalg.eig(M)
    k = np.argmin(np.abs(w - target))
    wl, U = np.linalg.eig(M.T)
    kl = np.argmin(np.abs(wl - w[k]))
    r = V[:, k]; l = U[:, kl]
    l = l / np.dot(l, r)
    return w[k], r, l


def tilt_residual(A, theta, beta, lam_prev):
    lam, r, l = eig_near(A - np.diag(theta), lam_prev)
    pi = l * r
    return np.concatenate([[lam], pi[1:] - beta[1:]]), lam, r, l


def solve_tilt(A, beta, theta0):
    theta = theta0.astype(complex).copy()
    g = len(beta)
    for it in range(60):
        F, lam, r, l = tilt_residual(A, theta, beta, 0.0)
        if np.max(np.abs(F)) < 1e-14:
            break
        Jm = np.zeros((g, g), complex)
        h = 1e-7
        for j in range(g):
            th = theta.copy(); th[j] += h
            Fj, *_ = tilt_residual(A, th, beta, lam)
            Jm[:, j] = (Fj - F) / h
        step = np.linalg.solve(Jm, -F)
        theta = theta + step
    F, lam, r, l = tilt_residual(A, theta, beta, 0.0)
    return theta, r, l, np.max(np.abs(F))


def tilt_path(D, beta, z, nsteps=20):
    """Continue the tilt from z = 0 (real Perron tilt) to complex z along a straight line."""
    A, *_ = weighted(D, 0.0)
    # real tilt at z = 0: start from theta = row sums, Newton
    theta = np.real(A).sum(axis=1).astype(complex)
    # damped continuation in beta from the stationary-like start
    theta, r, l, res = solve_tilt(A, beta, theta)
    for t in np.linspace(0, 1, nsteps + 1)[1:]:
        A, *_ = weighted(D, t * z)
        theta, r, l, res = solve_tilt(A, beta, theta)
    return theta, r, l, res


def constants(D, beta, z):
    A, d, mu, e = weighted(D, z)
    g = D['g']
    theta, r, l, res = tilt_path(D, beta, z)
    J = np.dot(d - theta, beta)
    # paper's constant: Sigma from the tilted generator Qhat = R^{-1}(A - Theta)R, stationary beta
    R = np.diag(r)
    Qh = np.linalg.solve(R, (A - np.diag(theta)) @ R)
    one = np.ones(g)
    Z = np.linalg.inv(np.outer(one, beta) - Qh) - np.outer(one, beta)
    Db = np.diag(beta)
    Gam = Db @ Z + Z.T @ Db
    Sig = Gam[1:, 1:]
    detS = np.linalg.det(Sig)
    Cpap = np.dot(mu, r) * np.dot(l, e) / ((2 * np.pi) ** ((g - 1) / 2) * np.sqrt(detS))
    return dict(theta=theta, r=r, l=l, J=J, C=Cpap, detSigma=detS, res=res, A=A, d=d, mu=mu, e=e)


def nu_of_psi(A, theta, beta, psi):
    """nu(psi) = u(psi) kappa(psi): the eigenvalue of u(psi) P_psi near 1 (computed via D_psi^{-1}A)."""
    g = len(theta)
    Dz = theta * np.exp(1j * psi)
    K = A / Dz[:, None]
    lam, _, _ = eig_near(K, 1.0)
    u = np.dot(beta, Dz) / np.dot(beta, theta)
    return u * lam


def spectral_constant(c, beta):
    """C from the spectral route: (2pi)^{-(g-1)/2} det(H_Phi)^{-1/2} a(0), H_Phi by finite differences."""
    A, theta, r, l, mu, e = c['A'], c['theta'], c['r'], c['l'], c['mu'], c['e']
    g = len(beta)
    T1 = np.dot(theta, beta)
    h = 1e-4
    H = np.zeros((g - 1, g - 1), complex)
    f0 = nu_of_psi(A, theta, beta, np.zeros(g))
    for a in range(1, g):
        for b in range(1, g):
            def f(sa, sb):
                p = np.zeros(g); p[a] += sa * h; p[b] += sb * h
                return nu_of_psi(A, theta, beta, p)
            H[a - 1, b - 1] = -(f(1, 1) - f(1, -1) - f(-1, 1) + f(-1, -1)) / (4 * h * h) * T1
    grad = []
    for a in range(1, g):
        p = np.zeros(g); p[a] = h
        q = np.zeros(g); q[a] = -h
        grad.append((nu_of_psi(A, theta, beta, p) - nu_of_psi(A, theta, beta, q)) / (2 * h))
    a0 = np.dot(mu, r) * np.dot(l, e) * np.prod(theta) / T1
    detH = np.linalg.det(H)
    Cspec = a0 / ((2 * np.pi) ** ((g - 1) / 2) * np.sqrt(detH))
    detpred = np.prod(theta) ** 2 * c['detSigma'] / T1 ** 2
    return dict(Cspec=Cspec, detH=detH, detpred=detpred, f0=f0, grad=np.array(grad), H=H)


def doob(c, beta):
    A, theta, r = c['A'], c['theta'], c['r']
    P0 = (A / theta[:, None]) * r[None, :] / r[:, None]
    w = theta * beta / np.dot(theta, beta)
    ev = np.linalg.eigvals(P0)
    return P0, w, ev


# ----------------------------------------------------------------------------------------------

def main():
    faces = make_faces()
    zs = [0.0, 0.08, 0.08j, -0.06 + 0.05j, 0.1 * np.exp(1j * 2.2)]
    print(__doc__)
    for name, Qoff, kill, i, muF, beta in faces:
        D = facet_data(Qoff, kill, i, muF)
        g = D['g']
        print('=' * 100)
        print(name)
        print('g =', g, ' beta =', beta)
        print('A0 =\n', np.real(D['A0']))
        print('q_G =', np.real(D['qG']), ' c^- =', np.real(D['cm']), ' c^+ =', np.real(D['cp']))

        # Part 1: representation vs word series
        print('\nPart 1. Representation (Lemma R) against the word series, s = S0*beta.')
        S0 = 1.2 if g == 4 else 1.6
        mmax = 13 if g == 4 else 22
        s = S0 * beta
        for z in [0.0, 0.3 - 0.4j]:
            ws = word_series(D, z, s, mmax)
            A, d, mu, e = weighted(D, z)
            th_real = np.real(A).sum(axis=1) + 0.5
            th_cplx = th_real * np.exp(1j * np.array([0.0, 0.3, -0.2, 0.5])[:g]) * (1.0 + 0.2j)
            for lab, th in [('real radii', th_real.astype(complex)), ('complex radii', th_cplx)]:
                I = rep_integral(D, z, s, th, N=48 if g == 4 else 64)
                rep = np.exp(-np.dot(d, s)) * np.exp(np.dot(s, th)) * I
                print(f'  z = {z!s:>12}  {lab:14s}  word series = {ws:.12e}  representation = {rep:.12e}'
                      f'  rel diff = {abs(rep / ws - 1):.2e}')

        # Part 2-3: tilt, Doob transform, constants
        print('\nPart 2. Complex tilt and Doob transform P_0 = R^{-1} Theta^{-1} A(z) R.')
        consts = {}
        for z in zs:
            c = constants(D, beta, z)
            consts[z] = c
            P0, w, ev = doob(c, beta)
            ev_sorted = sorted(ev, key=lambda x: -x.real)
            npr = [x for x in ev if abs(x - 1) > 1e-8]
            gam0 = 1 - max(x.real for x in npr)
            print(f'  z = {z!s:>22}  tilt residual {c["res"]:.1e}  theta = {np.round(c["theta"], 6)}')
            print(f'      row sums of P_0 - 1: {np.max(np.abs(P0.sum(axis=1) - 1)):.1e}   '
                  f'w = theta*beta/<theta,beta> = {np.round(w, 5)}')
            print(f'      eigenvalues of P_0: {np.round(np.array(ev_sorted), 5)}   gamma_0 = 1 - max Re(non-Perron) = {gam0:.4f}')
            print(f'      max row sum of |P_0| = {np.abs(P0).sum(axis=1).max():.5f},  sum |w_j| = {np.abs(w).sum():.5f}')
        print('\nPart 3. Constant of the spectral route against the paper\'s C_G(beta,z).')
        for z in zs:
            c = consts[z]
            sc = spectral_constant(c, beta)
            print(f'  z = {z!s:>22}  nu(0) - 1 = {abs(sc["f0"] - 1):.1e}  |grad nu(0)| = {np.max(np.abs(sc["grad"])):.1e}'
                  f'  det H / predicted = {sc["detH"] / sc["detpred"]:.8f}')
            print(f'      J = {c["J"]:.10f}   C_paper = {c["C"]:.10f}   C_spectral = {sc["Cspec"]:.10f}'
                  f'   min eig Re H = {np.linalg.eigvalsh(np.real(sc["H"])).min():.4f}')

        # Part 4: asymptotics
        print('\nPart 4. Exact f^{(z)}(S beta) against S^{-(g-1)/2} C e^{-S J}.  eps = ratio - 1.')
        Ss = [25, 50, 100, 200, 400] if g == 4 else [25, 50, 100, 200, 400, 800]
        for z in zs:
            c = consts[z]
            print(f'  z = {z}')
            for S in Ss:
                s = S * beta
                vals = []
                for N in ([56, 72] if g == 4 else [96, 128]):
                    Nn = N if S <= 100 else int(N * math.sqrt(S / 100.0))
                    I = rep_integral(D, z, s, c['theta'], N=Nn)
                    vals.append(I)
                ratio = vals[-1] / (S ** (-(g - 1) / 2) * c['C'])
                eps = ratio - 1
                print(f'    S = {S:4d}  ratio = {ratio.real:+.9f}{ratio.imag:+.9f}i   |eps| = {abs(eps):.3e}'
                      f'   S|eps| = {S * abs(eps):.4f}   grid change = {abs(vals[-1] / vals[0] - 1):.1e}')
            # a second, theory-free check of the exponent: real radii theta(beta,0) instead of the complex tilt
            S = 100
            s = S * beta
            th0 = consts[0.0]['theta']
            I0 = rep_integral(D, z, s, th0, N=(72 if g == 4 else 128))
            A, d, mu, e = weighted(D, z)
            Ic = rep_integral(D, z, s, c['theta'], N=(72 if g == 4 else 128))
            lhs = np.log(I0) + np.dot(s, th0)
            rhs = np.log(Ic) + np.dot(s, c['theta'])
            dlog = lhs - rhs
            dlog = complex(dlog.real, (dlog.imag + np.pi) % (2 * np.pi) - np.pi)
            print(f'    radius independence at S = 100: log f(real radii) - log f(complex tilt) = {dlog:.2e}')


if __name__ == '__main__':
    main()
