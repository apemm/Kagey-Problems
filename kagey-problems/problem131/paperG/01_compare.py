"""Compare the exact law of A_N with the predicted local laws in each region of the phase diagram.

Run:  py -I 01_compare.py      (about two minutes; writes 01_compare_output.txt next to this file)

Predictions P1-P7 are listed in 01_phase_diagram.md, Section 0. Zeta run laws throughout.
Stable laws: Z with Laplace exp(-Gamma(1-a) lam^a) for 0 < a < 1 (Levy tail x^-a), via scipy's
levy_stable in the S1 parameterization with beta = 1 and scale (Gamma(1-a) cos(pi a/2))^(1/a).
"""
import importlib.util
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import gamma, zeta
from scipy.stats import levy_stable

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('exact', HERE / '01_exact_law.py')
ex = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ex)
OUT = []
NS = [1000, 2000, 4000]


def log(s=''):
    print(s, flush=True)
    OUT.append(s)


def pos_stable(a):
    return levy_stable(a, 1.0, loc=0.0, scale=(gamma(1 - a) * np.cos(np.pi * a / 2)) ** (1 / a))


def phiE_table(a, xmax=12.0, n=6001):
    """Density of E = S^(-a), S positive a-stable as above (so phi_E(0) = 1), on a grid."""
    d = pos_stable(a)
    x = np.linspace(0, xmax, n)
    y = np.ones(n)
    y[1:] = d.pdf(x[1:] ** (-1 / a)) * x[1:] ** (-1 - 1 / a) / a
    y[~np.isfinite(y)] = 0.0
    return lambda t: np.interp(t, x, y, right=0.0)


def Tcont(a, x):
    return zeta(a + 1, x) / zeta(a + 1)


def modes(P):
    Q = np.concatenate(([-1.0], P, [-1.0]))
    return [k for k in range(len(P)) if Q[k + 1] > Q[k] and Q[k + 1] > Q[k + 2]]


def conv_powers(f, M, J):
    U = np.zeros((M + 1, J + 1))
    U[0, 0] = 1.0
    for m in range(1, M + 1):
        U[m] = np.convolve(U[m - 1], f[:J + 1])[:J + 1]
    return U


def mixture(U, Tp_n, phi):
    """T_+(n) sum_m u^-_m(j) phi_E(m T_+(n)), n = N - j, for each column j of U."""
    m = np.arange(U.shape[0])[:, None]
    return Tp_n * np.sum(U * phi(m * Tp_n[None, :]), axis=0)


def log_grid_pdf(d, lo, hi, n=30001):
    """Interpolant z -> pdf(z) of a positive law on a logarithmic grid (zero outside)."""
    t = np.linspace(lo, hi, n)
    g = d.pdf(np.exp(t))
    g[~np.isfinite(g)] = 0.0
    return t, g, lambda z: np.where(z > 0, np.interp(np.log(np.maximum(z, 1e-300)), t, g,
                                                      left=0.0, right=0.0), 0.0)


def rho_table(ap, am):
    """Density of S_- / S_+^(ap/am), S_+- independent positive stable as above."""
    beta = ap / am
    tt, gp, _ = log_grid_pdf(pos_stable(ap), -12, 70)
    _, _, gm = log_grid_pdf(pos_stable(am), -25, 60)
    ly = np.linspace(np.log(1e-6), np.log(1e3), 1201)
    r = np.array([np.trapezoid(gp * np.exp(tt * (1 + beta)) * gm(np.exp(l + tt * beta)), tt)
                  for l in ly])
    return lambda y: np.interp(np.log(np.maximum(y, 1e-6)), ly, r, right=0.0)


def dominated(name, ap, am, scale_kind, ytab, core, Nmax=4000):
    log(f'=== {name}: alpha_+ = {ap}, alpha_- = {am}, fresh plus start')
    fp, Tp = ex.zeta_law(ap, Nmax)
    fm, Tm = ex.zeta_law(am, Nmax)
    A, B = ex.run_arrays(fp, fm, Nmax)
    um = ex.renewal(fm, Nmax)
    up = ex.renewal(fp, Nmax)
    phi = phiE_table(ap)
    dens = rho_table(ap, am) if scale_kind == 'subordinator' else phi
    if scale_kind == 'subordinator':
        _, _, gm = log_grid_pdf(pos_stable(am), -25, 60)
    log('   columns per y = j/D_N: P/limit, P/(layer x bulk), P/mixture'
        + (', P/(limit with drift, post hoc)' if scale_kind == 'subordinator' else ''))
    for N in NS:
        P = ex.law(A, B, Tp, Tm, N)
        TN = Tp[N]
        if scale_kind == 'mean':
            mu = zeta(am) / zeta(am + 1)
            D = mu / TN
        elif scale_kind == 'subordinator':
            D = brentq(lambda x: Tcont(am, x) - TN, 1.0, 1e9)
        else:                                   # Cauchy domain, relatively stable lighter law
            a = brentq(lambda x: Tcont(am, x) - TN, 1.0, 1e12)
            D = np.sum(Tm[1:int(a) + 1]) / TN
        J = min(N - 1, int(1.05 * max(ytab) * D) + 1)
        j = np.arange(J + 1)
        y = j / D
        lim = dens(y) / D
        if scale_kind == 'subordinator':
            c = np.sin(np.pi * am) / np.pi
            psi = np.where(y > 0, dens(y) / (c * np.maximum(y, 1e-12) ** (am - 1)), 1.0)
            unified = TN * um[j] * psi
        elif scale_kind == 'mean':
            unified = TN * um[j] * phi(y)
        else:
            unified = np.full(J + 1, np.nan)
        M = int(min(N, 8 / TN))
        U = conv_powers(fm, M, J)
        mix = mixture(U, Tp[N - j], phi)
        ex_ = P[N - j]
        ok = (y >= core[0]) & (y <= core[1])
        msg = (f'N={N:5d}  D_N={D:8.2f}  core y in [{core[0]}, {core[1]}]: max |ratio-1| limit '
               f'{np.max(np.abs(ex_[ok] / lim[ok] - 1)):.3f}, mixture '
               f'{np.max(np.abs(ex_[ok] / mix[ok] - 1)):.4f}')
        if scale_kind != 'cauchy':
            ok2 = y <= core[1]
            msg += f'; layer x bulk on 0 <= y <= {core[1]}: {np.max(np.abs(ex_[ok2] / unified[ok2] - 1)):.3f}'
        log(msg)
        row = []
        for yy in ytab:
            jj = int(round(yy * D))
            r = f'{yy}: {ex_[jj] / lim[jj]:.3f} {ex_[jj] / unified[jj]:.3f} {ex_[jj] / mix[jj]:.4f}'
            if scale_kind == 'subordinator':
                # post hoc refinement: S^-_m ~ a_-(m) S_- + m mu*, mu* = zeta(am)/zeta(am+1)
                mus = zeta(am) / zeta(am + 1)
                x = np.linspace(1e-4, 12, 4000)
                t = x / TN
                aa = (t / (am * zeta(am + 1))) ** (1 / am)
                ref = np.trapezoid(phi(x) / aa * gm((jj - mus * t) / aa), x)
                r += f' {ex_[jj] / ref:.3f}'
            row.append(r)
        log('   ' + ' | '.join(row))
        log('   end layer P_N(N-j)/(T_+(N) u_-(j)), j=0..5: '
            + ' '.join(f'{P[N - i] / (TN * um[i]):.4f}' for i in range(6)))
        log('   minus-end layer P_N(i)/(T_-(N) u_+(i)), i=1..5: '
            + ' '.join(f'{P[i] / (Tm[N] * up[i]):.4f}' for i in range(1, 6)))
        ks = []
        for v in [0.2, 0.35, 0.5, 0.65, 0.8, 0.95]:
            jj = int(v * N)
            n = N - jj
            ker = up[1:n].sum() * fm[jj] + Tm[jj] * up[n]
            ks.append(f'{v}: {P[N - jj] / ker:.3f}')
        log('   big-jump kernel P/[gamma_+(n) f_-(j) + T_-(j) u_+(n)] at j = vN (n = N - j): '
            + ' '.join(ks))
        md = modes(P)
        log(f'   strict local maxima at k = {md[:8]} (N - k = {[N - k for k in md[:8]]})')
    if scale_kind == 'mean':
        xs = np.linspace(0, 3, 30001)
        log(f'   mode of phi_E: y* = {xs[np.argmax(phi(xs))]:.3f}, max phi_E = {phi(xs).max():.4f}, '
            f'mu_- = {zeta(am) / zeta(am + 1):.4f}')
    log()


def finite_mean_unequal(ap, am, Nmax=4000):
    log(f'=== P4 finite means: alpha_+ = {ap}, alpha_- = {am}, fresh plus start (Paper F region)')
    fp, Tp = ex.zeta_law(ap, Nmax)
    fm, Tm = ex.zeta_law(am, Nmax)
    A, B = ex.run_arrays(fp, fm, Nmax)
    mup, mum = zeta(ap) / zeta(ap + 1), zeta(am) / zeta(am + 1)
    s = mup + mum
    p = mup / s
    for N in NS:
        P = ex.law(A, B, Tp, Tm, N)
        bp = brentq(lambda x: Tcont(ap, x) - s / N, 1.0, 1e9)
        bm = brentq(lambda x: Tcont(am, x) - s / N, 1.0, 1e9)
        BN = max(bp, bm)
        th = (bp / BN, bm / BN)
        Kp, Km = -gamma(1 - ap), -gamma(1 - am)

        def h(x):
            def integrand(t):
                z = (Kp * ((1 - p) * th[0]) ** ap * t ** ap * np.exp(-1j * np.pi * ap / 2)
                     + Km * (p * th[1]) ** am * t ** am * np.exp(1j * np.pi * am / 2))
                return (np.exp(z - 1j * t * x)).real
            return quad(integrand, 0, np.inf, limit=400)[0] / np.pi
        ks = np.arange(int(p * N - 2 * BN), int(p * N + 2 * BN) + 1)
        xs = (ks - p * N) / BN
        xg = np.linspace(xs[0] - 0.05, xs[-1] + 0.05, 121)
        hg = np.array([h(x) for x in xg])
        hv = np.interp(xs, xg, hg)
        e = np.max(np.abs(BN * P[ks] / hv - 1))
        log(f'N={N:5d}  B_N={BN:7.2f}  theta=({th[0]:.3f},{th[1]:.3f})  '
            f'max rel err of B_N P_N vs h_N on |x|<=2: {e:.3f}')
        log('   B_N P_N / h_N at x = ' + ' '.join(
            f'{x}: {BN * P[int(round(p * N + x * BN))] / np.interp(x, xg, hg):.3f}'
            for x in [-2.0, -1.5, -1.0, -0.5, 0.0, 0.5, 1.0, 1.5, 2.0]))
    log()


def balanced(a, Nmax=4000):
    log(f'=== P5 balanced infinite mean: alpha_+ = alpha_- = {a}, b = 1 (Paper G region)')
    f, T = ex.zeta_law(a, Nmax)
    A, B = ex.run_arrays(f, f, Nmax)
    for N in NS:
        P = ex.law(A, B, T, T, N)
        k = np.arange(int(0.1 * N), int(0.9 * N) + 1)
        x = k / N
        L = (np.sin(np.pi * a) / np.pi * x ** (a - 1) * (1 - x) ** (a - 1)
             / (x ** (2 * a) + 2 * np.cos(np.pi * a) * x ** a * (1 - x) ** a + (1 - x) ** (2 * a)))
        log(f'N={N:5d}  max |N P_N(k) - L(k/N)| on [0.1N, 0.9N]: {np.max(np.abs(N * P[k] - L)):.4f}')
        log('   N P_N / L at k/N = ' + ' '.join(
            f'{xx}: {N * P[int(xx * N)] / np.interp(xx, x, L):.3f}' for xx in [0.1, 0.25, 0.5, 0.75, 0.9]))
    log()


def modes_only(ap, am, Nmax=4000):
    log(f'=== P7 (added after P1-P6 ran) mixed with alpha_+ = {ap} < 1/2, alpha_- = {am}: modes')
    fp, Tp = ex.zeta_law(ap, Nmax)
    fm, Tm = ex.zeta_law(am, Nmax)
    for start in '+-':
        A, B = ex.run_arrays(fp, fm, Nmax, start)
        um = ex.renewal(fm, 6)
        for N in NS:
            P = ex.law(A, B, Tp, Tm, N)
            md = modes(P)
            lay = ' '.join(f'{P[N - i] / (Tp[N] * um[i]):.4f}' for i in range(6))
            log(f'start {start} N={N:5d}: strict local maxima at k = {md[:8]}; '
                f'P_N(N-j)/(T_+(N) u_-(j)), j=0..5: {lay}')
    log()


if __name__ == '__main__':
    d = pos_stable(0.7)
    y = 1.3
    r = quad(lambda s: d.pdf(s) * s * d.pdf(y * s), 0, np.inf, limit=400)[0]
    c = np.sin(0.7 * np.pi) / np.pi * y ** (-0.3) / (1 + 2 * y ** 0.7 * np.cos(0.7 * np.pi) + y ** 1.4)
    log(f'check: ratio density of two 0.7-stables at y=1.3: quadrature {r:.10f}, closed form {c:.10f}')
    phi = phiE_table(0.5)
    log(f'check: phi_E for alpha=1/2 equals exp(-pi x^2/4): at x=0.7 {phi(0.7):.8f} vs '
        f'{np.exp(-np.pi * 0.49 / 4):.8f}')
    log()
    dominated('P1 mixed', 0.6, 1.5, 'mean', [0.05, 0.1, 0.2, 0.3, 0.5, 0.75, 1.0, 1.5, 2.0],
              (0.05, 1.0))
    dominated('P2 unequal infinite means', 0.5, 0.8, 'subordinator',
              [0.05, 0.1, 0.25, 0.5, 1.0, 2.0, 3.0, 5.0], (0.1, 3.0))
    dominated('P6 boundary, lighter law in the Cauchy domain', 0.6, 1.0, 'cauchy',
              [0.05, 0.1, 0.2, 0.3, 0.5, 0.75, 1.0, 1.5, 2.0], (0.05, 1.0))
    finite_mean_unequal(1.3, 1.8)
    balanced(0.7)
    modes_only(0.4, 1.5)
    (HERE / '01_compare_output.txt').write_text('\n'.join(OUT) + '\n', newline='\n')
