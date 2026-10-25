"""Audit checks for the note 10_hypL_spectral_route.md (Hypothesis L by the spectral route).

Run with:  py -I 11_hypL_audit_check.py > 11_hypL_audit_output.txt

Part A. Lemma CL in one dimension, from scratch. A complex phase Phi with Re(-Phi''(0)) > 0 is
        integrated over a fixed interval and compared with e^{S Phi(0)} sqrt(2 pi/(S h)) a(0).
        The 1/S coefficient is also computed in closed form from the Gaussian moments, so the
        plateau of S*rho has a predicted limit.
Part B. Two facets with g = 4 states that the note did not run: the 4-path and the 4-star, both
        with a bipartite jump chain. For each: Lemma R against the word series, the complex tilt,
        the spectrum of P_0 (eigenvalue -1 present), the twisted kernel at the bipartition
        character (an eigenvalue of modulus one, and u = 0 there), a grid scan of |u(psi)| and of
        the spectral abscissa of Y_psi away from the identity character, and the S|eps| table of
        Hypothesis L with the paper's constant C_G(beta,z).
Part C. Lemma H for two states against the closed forms H_Phi = sqrt(tau beta_1 beta_2)/2 and the
        constant of Lemma lem:L-two.
"""
import importlib
import itertools
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
m10 = importlib.import_module('10_hypL_spectral_check')

np.set_printoptions(linewidth=140, precision=6)


# ----------------------------------------------------------------------------------------------
# Part A: Lemma CL, one dimension
# ----------------------------------------------------------------------------------------------

def gauss_legendre_integral(f, lo, hi, panels=64, nodes=48):
    x, w = np.polynomial.legendre.leggauss(nodes)
    total = 0j
    edges = np.linspace(lo, hi, panels + 1)
    for a, b in zip(edges[:-1], edges[1:]):
        xs = 0.5 * (b - a) * x + 0.5 * (b + a)
        total += 0.5 * (b - a) * np.sum(w * f(xs))
    return total


def part_a():
    print('=' * 100)
    print('Part A. Lemma CL in one dimension.')
    h = 1.0 + 0.8j            # -Phi''(0), Re h = 1 > 0
    c3 = 0.3 - 0.1j
    c4 = 0.05j
    a0, a1, a2 = 1.0, 0.4, 0.2j
    eps = 0.5
    Phi = lambda p: -0.5 * h * p ** 2 + c3 * p ** 3 + c4 * p ** 4
    a = lambda p: a0 + a1 * p + a2 * p ** 2
    # predicted 1/S coefficient of rho: terms of order 1/S in e^w a(x/sqrt S) with
    # w = c3 x^3/sqrt S + c4 x^4/S, against the normalized Gaussian with E x^{2n} = (2n-1)!!/h^n
    rho1 = a0 * (15 * c3 ** 2 / (2 * h ** 3) + 3 * c4 / h ** 2) + 3 * a1 * c3 / h ** 2 + a2 / h
    print(f'  Phi(psi) = -(h/2) psi^2 + c3 psi^3 + c4 psi^4, h = {h}, c3 = {c3}, c4 = {c4}')
    print(f'  a(psi) = {a0} + {a1} psi + {a2} psi^2, interval [-{eps}, {eps}]')
    print(f'  predicted limit of S*rho: {rho1:.6f}  (|.| = {abs(rho1):.6f})')
    for S in [25, 50, 100, 200, 400, 800, 1600, 3200]:
        f = lambda p: np.exp(S * Phi(p)) * a(p)
        I = gauss_legendre_integral(f, -eps, eps, panels=max(64, int(8 * math.sqrt(S))), nodes=48)
        lead = np.sqrt(2 * np.pi / (S * h))      # principal branch; Re h > 0
        rho = I / lead - a0
        print(f'    S = {S:5d}  rho = {rho.real:+.6e}{rho.imag:+.6e}i   S*rho = {S * rho:.6f}   |S*rho - rho1| = {abs(S * rho - rho1):.2e}')
    print('  The error after removing the 1/S term should be O(1/S^2): the last column halves four times per doubling of S if quadratic.')


# ----------------------------------------------------------------------------------------------
# Part B: two facets with g = 4
# ----------------------------------------------------------------------------------------------

def make_faces():
    faces = []
    # (e) G = path 0-1-2-3 with unequal rates; i = 4 entered from 3 (rate 1.3) and 0 (rate 0.4),
    #     left to 0 (rate 1.0) and 2 (rate 0.6). Killing 0.2 on every state.
    k = 5
    Q = np.zeros((k, k))
    Q[0, 1] = 2.0; Q[1, 0] = 1.0
    Q[1, 2] = 1.5; Q[2, 1] = 0.7
    Q[2, 3] = 2.2; Q[3, 2] = 1.1
    Q[3, 4] = 1.3; Q[0, 4] = 0.4
    Q[4, 0] = 1.0; Q[4, 2] = 0.6
    faces.append(('G = 4-path 0-1-2-3 (unequal rates), i = 4 entered from 3,0 and left to 0,2',
                  Q, np.full(k, 0.2), 4, np.array([0.3, 0.15, 0.2, 0.2, 0.15]),
                  np.array([0.3, 0.2, 0.25, 0.25])))
    # (f) G = star with centre 0 and leaves 1,2,3; i = 4 entered from leaf 1, left to leaf 3 and centre 0.
    Q = np.zeros((k, k))
    Q[0, 1] = 1.0; Q[0, 2] = 2.0; Q[0, 3] = 0.5
    Q[1, 0] = 1.5; Q[2, 0] = 0.8; Q[3, 0] = 2.5
    Q[1, 4] = 1.0
    Q[4, 3] = 1.2; Q[4, 0] = 0.3
    faces.append(('G = 4-star (centre 0, leaves 1,2,3), i = 4 entered from 1 and left to 3,0',
                  Q, np.full(k, 0.1), 4, np.array([0.2, 0.2, 0.2, 0.2, 0.2]),
                  np.array([0.35, 0.2, 0.25, 0.2])))
    return faces


def tilt_newton(A, beta, psi0, real_case, iters=200):
    """Solve the tilt equations for A (g x g, zero diagonal) and beta in the coordinates u = e^psi,
    psi_1 = 0. The equations are grad_psi Psi = 0 with Psi(psi) = -sum_{j != j'} beta_j A_{jj'} e^{psi_j' - psi_j};
    they say l^T (A - diag theta) = 0 for l = beta/u, theta = A u / u. For real nonnegative A the
    function Psi is concave and Newton with backtracking converges from any start. For complex A the
    same Newton step is used, with the continuation in z supplying the start."""
    g = len(beta)
    psi = psi0.astype(complex).copy()

    def pieces(psi):
        u = np.exp(psi)
        M = beta[:, None] * A * (u[None, :] / u[:, None])
        val = -M.sum()
        grad = -M.sum(axis=0) + M.sum(axis=1)
        H = M + M.T
        np.fill_diagonal(H, -M.sum(axis=0) - M.sum(axis=1))
        return u, val, grad, H

    for it in range(iters):
        u, val, grad, H = pieces(psi)
        if np.max(np.abs(grad[1:])) < 1e-14:
            break
        step = np.linalg.solve(H[1:, 1:], -grad[1:])
        t = 1.0
        if real_case:
            while t > 1e-6:
                trial = psi.copy(); trial[1:] += t * step
                if pieces(trial)[1].real > val.real:
                    break
                t *= 0.5
        psi[1:] += t * step
    u, val, grad, H = pieces(psi)
    theta = (A @ u) / u
    r = u / u[0]
    l = beta / r
    return theta, r, l, np.max(np.abs(grad[1:])), psi


def my_tilt_path(D, beta, z, nsteps=40):
    A, *_ = m10.weighted(D, 0.0)
    theta, r, l, res, psi = tilt_newton(np.real(A), beta, np.zeros(len(beta)), True)
    for t in np.linspace(0, 1, nsteps + 1)[1:]:
        A, *_ = m10.weighted(D, t * z)
        theta, r, l, res, psi = tilt_newton(A, beta, psi, False)
    return theta, r, l, res


m10.tilt_path = my_tilt_path


def cross_check_tilt():
    """The independent tilt solver against the values printed by the note's script for its face (c)."""
    print('=' * 100)
    print("Cross-check of the independent tilt solver on the note's face (c), z = 0.08i.")
    name, Qoff, kill, i, muF, beta = m10.make_faces()[2]
    D = m10.facet_data(Qoff, kill, i, muF)
    theta, r, l, res = my_tilt_path(D, beta, 0.08j)
    print('  theta =', np.round(theta, 6), ' residual', f'{res:.1e}')
    print('  compare with the line "z = 0.08j ... theta =" under face (c) in 10_hypL_spectral_output.txt')


def bipartition_character(P0):
    """For a bipartite zero-diagonal stochastic P0 return psi with psi = pi on one part (psi_0 = 0)."""
    g = P0.shape[0]
    colour = [None] * g
    colour[0] = 0
    stack = [0]
    adj = np.abs(P0) > 1e-12
    while stack:
        a = stack.pop()
        for b in range(g):
            if adj[a, b] or adj[b, a]:
                if colour[b] is None:
                    colour[b] = 1 - colour[a]
                    stack.append(b)
                elif colour[b] == colour[a]:
                    return None
    return np.array([math.pi if c == 1 else 0.0 for c in colour])


def part_b():
    zs = [0.0, 0.08, 0.08j, -0.06 + 0.05j]
    for name, Qoff, kill, i, muF, beta in make_faces():
        D = m10.facet_data(Qoff, kill, i, muF)
        g = D['g']
        print('=' * 100)
        print(name)
        print('g =', g, ' beta =', beta)
        print('A0 =\n', np.real(D['A0']))
        print('q_G =', np.real(D['qG']), ' c^- =', np.real(D['cm']), ' c^+ =', np.real(D['cp']),
              ' mu_G =', np.real(D['muG']), ' mu_i =', D['mui'].real)

        print('\nB1. Lemma R against the word series at s = 1.2*beta (word series truncated at 13 letters per state).')
        s = 1.2 * beta
        for z in [0.0, 0.3 - 0.4j]:
            ws = m10.word_series(D, z, s, 13)
            A, d, mu, e = m10.weighted(D, z)
            th_real = np.real(A).sum(axis=1) + 0.5
            th_cplx = th_real * np.exp(1j * np.array([0.0, 0.3, -0.2, 0.5])) * (1.0 + 0.2j)
            for lab, th in [('real radii', th_real.astype(complex)), ('complex radii', th_cplx)]:
                I = m10.rep_integral(D, z, s, th, N=48)
                rep = np.exp(-np.dot(d, s)) * np.exp(np.dot(s, th)) * I
                print(f'  z = {z!s:>12}  {lab:14s}  word series = {ws:.12e}  representation = {rep:.12e}'
                      f'  rel diff = {abs(rep / ws - 1):.2e}')

        print('\nB2. Complex tilt, Doob transform, spectrum of P_0, twisted kernel at the bipartition character.')
        consts = {}
        for z in zs:
            c = m10.constants(D, beta, z)
            consts[z] = c
            P0, w, ev = m10.doob(c, beta)
            ev_sorted = sorted(ev, key=lambda x: -x.real)
            npr = [x for x in ev if abs(x - 1) > 1e-8]
            gam0 = 1 - max(x.real for x in npr)
            print(f'  z = {z!s:>14}  tilt residual {c["res"]:.1e}  theta = {np.round(c["theta"], 6)}')
            print(f'      row sums of P_0 - 1: {np.max(np.abs(P0.sum(axis=1) - 1)):.1e}   w = {np.round(w, 5)}   sum w = {w.sum():.6f}')
            print(f'      eigenvalues of P_0: {np.round(np.array(ev_sorted), 5)}   gamma_0 = {gam0:.4f}')
            if z == 0.0:
                psi_b = bipartition_character(np.real(P0))
                if psi_b is not None:
                    E = np.diag(np.exp(-1j * psi_b))
                    Pb = E @ P0
                    evb = np.linalg.eigvals(Pb)
                    ub = np.dot(w, np.exp(1j * psi_b))
                    Yb = ub * Pb
                    print(f'      bipartition character psi = {np.round(psi_b, 4)}:')
                    print(f'        |eigenvalues of P_psi| = {np.round(np.abs(evb), 6)}  (modulus one occurs)')
                    print(f'        u(psi) = {ub:.3e}   (mass of each part = 1/2, so u = 0 and exp(T Y_psi) = I)')
                    print(f'        max Re eig(Y_psi) = {np.max(np.linalg.eigvals(Yb).real):.3e}')
                # grid scan away from the identity character
                grid = np.linspace(0, 2 * np.pi, 25, endpoint=False)
                worst_u, worst_abs = 0.0, -10.0
                for p in itertools.product(grid, repeat=g - 1):
                    psi = np.array((0.0,) + p)
                    dist = np.max(np.abs((psi + np.pi) % (2 * np.pi) - np.pi))
                    if dist < 0.3:
                        continue
                    u = np.dot(w, np.exp(1j * psi))
                    worst_u = max(worst_u, abs(u))
                    Y = u * (np.diag(np.exp(-1j * psi)) @ P0)
                    worst_abs = max(worst_abs, np.max(np.linalg.eigvals(Y).real))
                print(f'      grid scan over |psi|_inf >= 0.3 (25^3 points): max |u(psi)| = {worst_u:.5f},'
                      f' max spectral abscissa of Y_psi = {worst_abs:.5f}  (both < 1)')
                print(f'      (S2) bound 1 - w_min^2 (1 - cos 0.3) = {1 - np.min(np.real(w)) ** 2 * (1 - math.cos(0.3)):.5f}')

        print('\nB3. Spectral constant against the paper constant (Lemma H), and Re H_Phi.')
        for z in zs:
            c = consts[z]
            sc = m10.spectral_constant(c, beta)
            print(f'  z = {z!s:>14}  nu(0) - 1 = {abs(sc["f0"] - 1):.1e}  |grad nu(0)| = {np.max(np.abs(sc["grad"])):.1e}'
                  f'  det H / predicted = {sc["detH"] / sc["detpred"]:.8f}')
            print(f'      J = {c["J"]:.10f}   C_paper = {c["C"]:.10f}   C_spectral = {sc["Cspec"]:.10f}'
                  f'   min eig Re H = {np.linalg.eigvalsh(np.real(sc["H"])).min():.4f}')

        print('\nB4. Hypothesis L: eps = f^{(z)}(S beta) / (S^{-3/2} C_G(beta,z) e^{-S J_G(beta,z)}) - 1.')
        for z in zs:
            c = consts[z]
            print(f'  z = {z}')
            for S in [25, 50, 100, 200, 400]:
                s = S * beta
                vals = []
                for N in [48, 64]:
                    Nn = N if S <= 100 else int(N * math.sqrt(S / 100.0))
                    vals.append(m10.rep_integral(D, z, s, c['theta'], N=Nn))
                ratio = vals[-1] / (S ** (-(g - 1) / 2) * c['C'])
                eps = ratio - 1
                print(f'    S = {S:4d}  ratio = {ratio.real:+.9f}{ratio.imag:+.9f}i   |eps| = {abs(eps):.3e}'
                      f'   S|eps| = {S * abs(eps):.4f}   grid change = {abs(vals[-1] / vals[0] - 1):.1e}')


# ----------------------------------------------------------------------------------------------
# Part C: Lemma H for two states
# ----------------------------------------------------------------------------------------------

def part_c():
    print('=' * 100)
    print('Part C. Lemma H and the constant for two states.')
    a, b = 1.7, 0.6              # A(z) = [[0,a],[b,0]] at some real z
    p = np.array([0.4, 0.9])     # mu^(z)
    e = np.array([1.3, 1.0])     # e^(z)
    beta = np.array([0.35, 0.65])
    tau = a * b
    th1 = math.sqrt(tau * beta[1] / beta[0]); th2 = math.sqrt(tau * beta[0] / beta[1])
    theta = np.array([th1, th2])
    A = np.array([[0, a], [b, 0]], complex)
    T1 = np.dot(theta, beta)
    h = 1e-4
    f = lambda phi: m10.nu_of_psi(A, theta.astype(complex), beta, np.array([0.0, phi]))
    H = -(f(h) - 2 * f(0.0) + f(-h)) / h ** 2 * T1
    print(f'  a = {a}, b = {b}, beta = {beta}, theta = {theta}, <theta,beta> = {T1:.8f} = 2 sqrt(tau b1 b2) = {2 * math.sqrt(tau * beta[0] * beta[1]):.8f}')
    print(f'  nu(phi) finite differences: H_Phi = {H.real:.8f}{H.imag:+.1e}i,  closed form sqrt(tau b1 b2)/2 = {math.sqrt(tau * beta[0] * beta[1]) / 2:.8f},'
          f'  cos(phi/2) check: nu(0.7) = {f(0.7).real:.8f}, cos(0.35) = {math.cos(0.35):.8f}')
    # paper's det Sigma for the two-state tilted generator with rates theta_1, theta_2
    detS = 2 * th1 * th2 / (th1 + th2) ** 3
    print(f'  det Theta^2 det Sigma / <theta,beta>^2 = {tau ** 2 * detS / T1 ** 2:.8f}')
    # constants
    r = np.array([1.0, th1 / a]); l = beta / r
    a0 = np.dot(p, r) * np.dot(l, e) * th1 * th2 / T1
    Cspec = a0 / math.sqrt(2 * math.pi * H.real)
    U = p[0] * e[0] * math.sqrt(tau * beta[0] / beta[1]) + p[1] * e[1] * math.sqrt(tau * beta[1] / beta[0])
    V = p[0] * a * e[1] + p[1] * b * e[0]
    Ctwo = (U + V) / (math.sqrt(4 * math.pi) * (tau * beta[0] * beta[1]) ** 0.25)
    print(f'  C_spectral = {Cspec:.10f}   C (Lemma lem:L-two) = {Ctwo:.10f}   rel diff = {abs(Cspec / Ctwo - 1):.1e}')


if __name__ == '__main__':
    print(__doc__)
    part_a()
    part_c()
    cross_check_tilt()
    part_b()
