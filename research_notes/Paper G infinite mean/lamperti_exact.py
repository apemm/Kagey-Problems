"""Paper G (infinite-mean regime): exact law of the occupation count and the local Lamperti law.

Run:  py -I lamperti_exact.py            (all checks, about a few minutes)
      py -I lamperti_exact.py --quick    (N up to 2000 only)

Setting. Alternating runs, symmetric zeta laws f(n) = n^(-a-1)/zeta(a+1), 0 < a < 1. The exact law is
computed from the bivariate renewal arrays
    A(k, j) = sum_m u_m(k) u_m(j),        B(k, j) = sum_{m>=1} u_m(k) u_{m-1}(j),
with u_m = f^{*m} (computed by direct convolution, all terms nonnegative). A(k, j) is the probability
that a plus run starts after exactly k plus and j minus steps, for a fresh plus start, and B(k, j)
the same for a minus run. Splitting on the run in progress at step N gives, with j = N - k,
    F+_N(k) = sum_{k'<k} A(k', j) T(k-k') + sum_{j'<j} B(k, j') T(j-j').
The fair start is (F+_N(k) + F+_N(N-k))/2 by symmetry. This is independent of the plan's script.

Checks: brute force over sign strings (N <= 12, exact rationals replaced by floats of exact sums);
the ratio N P_N(k)/L(k/N); sign changes of the first difference; the end profile; the uniform
boundary-layer ratio; the U/W threshold cos(pi a/2) = a; the integral representation of L at a = 1/2.
Output goes to stdout and to lamperti_exact_output.txt next to this script.
"""
import sys
import time
import hashlib
import itertools
from pathlib import Path

import numpy as np
from scipy.special import zeta
from scipy.integrate import quad
from scipy.optimize import brentq

HERE = Path(__file__).resolve().parent
OUT = []


def log(s=""):
    print(s, flush=True)
    OUT.append(s)


def laws(a, nmax):
    z = zeta(a + 1)
    n = np.arange(nmax + 2, dtype=float)
    f = np.zeros(nmax + 2)
    f[1:] = n[1:] ** (-a - 1) / z
    T = np.ones(nmax + 2)
    T[1:] = zeta(a + 1, n[1:]) / z          # Hurwitz zeta: T(n) = P(X >= n)
    return f, T


def convolution_powers(f, nmax):
    U = np.zeros((nmax + 1, nmax + 1))
    U[0, 0] = 1.0
    for m in range(1, nmax + 1):
        prev = U[m - 1, m - 1:]                # u_{m-1} vanishes below m-1
        c = np.convolve(prev, f[1:nmax + 2 - m])   # shift: f starts at 1
        U[m, m:] = c[:nmax + 1 - m]
    return U


def arrays(f, nmax):
    U = convolution_powers(f, nmax)
    A = U.T @ U
    B = U[1:].T @ U[:-1]
    return U, A, B


def fresh_plus(A, B, T, N, Tm=None):
    Tm = T if Tm is None else Tm
    P = np.zeros(N + 1)
    for k in range(N + 1):
        j = N - k
        s = 0.0
        if k >= 1:
            s += A[0:k, j] @ T[k:0:-1]
        if j >= 1:
            s += B[k, 0:j] @ Tm[j:0:-1]
        P[k] = s
    return P


def lamperti(x, a, b=1.0):
    c = np.cos(np.pi * a)
    return (np.sin(np.pi * a) / np.pi * b * x ** (a - 1) * (1 - x) ** (a - 1)
            / (b * b * x ** (2 * a) + 2 * b * c * x ** a * (1 - x) ** a + (1 - x) ** (2 * a)))


def sign_changes(P):
    s = np.sign(np.diff(P))
    s = s[s != 0]
    return int(np.sum(s[1:] != s[:-1])), s


def brute(f, T, N):
    """Fresh plus start, sum over all sign strings starting with +."""
    P = np.zeros(N + 1)
    for rest in itertools.product((0, 1), repeat=N - 1):
        s = (1,) + rest
        runs = [len(list(g)) for _, g in itertools.groupby(s)]
        p = 1.0
        for r in runs[:-1]:
            p *= f[r]
        p *= T[runs[-1]]
        P[sum(s)] += p
    return P


def main():
    quick = '--quick' in sys.argv
    Ns = (1000, 2000) if quick else (1000, 2000, 4000)
    nmax = max(Ns)
    log('# script: lamperti_exact.py' + (' --quick' if quick else ''))
    log('# sha256: ' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    t0 = time.time()

    # P3: brute force
    worst = 0.0
    for a in (0.3, 0.7):
        f, T = laws(a, 20)
        _, A, B = arrays(f, 14)
        for N in range(1, 13):
            d = np.max(np.abs(brute(f, T, N) - fresh_plus(A, B, T, N)))
            worst = max(worst, d)
    log(f'P3 brute force N<=12, a in (0.3, 0.7): max abs difference {worst:.2e}')

    xs = [0.05, 0.1, 0.2, 0.3, 0.4, 0.5]
    for a in (0.3, 0.5, 0.7, 0.9):
        f, T = laws(a, nmax)
        _, A, B = arrays(f, nmax)
        z1 = f[1]
        log(f'\nalpha = {a}:  f(1) = {z1:.4f}  (fair-start end profile kappa(0)=1/2 vs kappa(1)=f(1))')
        log('   ratio N P_N(k)/L(k/N) at x = ' + ' '.join(f'{x:5.2f}' for x in xs))
        for N in Ns:
            Pp = fresh_plus(A, B, T, N)
            P = 0.5 * (Pp + Pp[::-1])
            r = [N * P[round(x * N)] / lamperti(round(x * N) / N, a) for x in xs]
            nch, s = sign_changes(P)
            pos = np.nonzero(s[1:] != s[:-1])[0] + 1
            log(f'   N={N}: ' + ' '.join(f'{v:6.4f}' for v in r)
                + f'  | sign changes {nch} at k = {list(pos)}  | total mass {P.sum():.12f}')
        Uu = convolution_powers(f, 12).sum(axis=0)
        kap = Uu.copy(); kap[0] = 0.5
        for N in Ns:
            Pp = fresh_plus(A, B, T, N)
            P = 0.5 * (Pp + Pp[::-1])
            log(f'   P7 N={N}: P_N(N-j)/(T(N) kappa(j)), j=0..5: '
                + ' '.join(f'{P[N - j] / (T[N] * kap[j]):.4f}' for j in range(6)))
        # P8: uniform boundary layer ratio with the full renewal sequence
        U = convolution_powers(f, nmax)
        ufull = U.sum(axis=0)
        c = np.cos(np.pi * a)
        for N in Ns:
            Pp = fresh_plus(A, B, T, N)
            P = 0.5 * (Pp + Pp[::-1])
            js = np.arange(1, int(0.8 * N) + 1)
            y = js / N
            Phi = (1 - y) ** (a - 1) / ((1 - y) ** (2 * a) + y ** (2 * a) + 2 * c * (1 - y) ** a * y ** a)
            rr = P[N - js] / (T[N] * ufull[js] * Phi)
            jsel = [1, 10, 100, N // 10, N // 2, int(0.8 * N)]
            log(f'   P8 N={N}: ratio at j = {jsel}: '
                + ' '.join(f'{rr[j - 1]:.4f}' for j in jsel)
                + f'  | min {rr.min():.4f} max {rr.max():.4f}')
            mass_end = P[: int(N ** 0.5)].sum() + P[N - int(N ** 0.5) + 1:].sum()
            log(f'   P9 N={N}: mass within sqrt(N) of the ends {mass_end:.5f}'
                f'  (Lamperti mass 2*int_0^(N^-1/2) L = '
                f'{2 * quad(lambda x: lamperti(x, a), 0, N ** -0.5)[0]:.5f})')
        log(f'   [elapsed {time.time() - t0:.0f} s]')


    # asymmetric check: plus zeta law, minus Hurwitz law f(n) = (n+3)^(-a-1)/zeta(a+1, 4), same index,
    # b = lim T-/T+ = zeta(a+1)/zeta(a+1, 4); fresh plus start
    for a in (0.5, 0.7):
        fp, Tp = laws(a, nmax)
        z4 = zeta(a + 1, 4)
        n = np.arange(nmax + 2, dtype=float)
        fm = np.zeros(nmax + 2); fm[1:] = (n[1:] + 3) ** (-a - 1) / z4
        Tmn = np.ones(nmax + 2); Tmn[1:] = zeta(a + 1, n[1:] + 3) / z4
        b = zeta(a + 1) / z4
        Up = convolution_powers(fp, nmax); Um = convolution_powers(fm, nmax)
        A2 = Up.T @ Um; B2 = Up[1:].T @ Um[:-1]
        log(f'\nasymmetric a={a}, b={b:.4f}, fresh plus: ratio N P_N(k)/L_b(k/N) at x = ' + ' '.join(f'{x:4.2f}' for x in (0.1, 0.3, 0.5, 0.7, 0.9)))
        for N in Ns:
            P = fresh_plus(A2, B2, Tp, N, Tmn)
            r = [N * P[round(x * N)] / lamperti(round(x * N) / N, a, b) for x in (0.1, 0.3, 0.5, 0.7, 0.9)]
            log(f'   N={N}: ' + ' '.join(f'{v:6.4f}' for v in r) + f'  | sign changes {sign_changes(P)[0]}  | mass {P.sum():.12f}')
        del Up, Um, A2, B2

    # P5 at finite N: fair start near the threshold
    for a in (0.56, 0.62):
        f, T = laws(a, nmax)
        _, A, B = arrays(f, nmax)
        for N in Ns:
            Pp = fresh_plus(A, B, T, N); P = 0.5 * (Pp + Pp[::-1])
            log(f'P5 finite N: a={a} N={N}: sign changes {sign_changes(P)[0]}')

    # P5: threshold of the symmetric Lamperti density
    ac = brentq(lambda a: np.cos(np.pi * a / 2) - a, 0.3, 0.9)
    log(f'\nP5 root of cos(pi a/2) = a: {ac:.10f}')
    for a in (0.55, 0.59, 0.60, 0.65, 0.8, 0.95):
        x = np.linspace(1e-4, 1 - 1e-4, 200001)
        L = lamperti(x, a)
        nch, _ = sign_changes(L)
        log(f'   a = {a}: critical points of L on (0,1): {nch}')

    # P4: the integral representation at a = 1/2 (positive 1/2-stable density, Laplace exp(-sqrt(pi l)))
    a = 0.5

    def g(z):
        return 0.0 if z <= 0 else 0.5 * z ** -1.5 * np.exp(-np.pi / (4 * z))

    def p(t, z):                       # density of the limit subordinator at time t: scale t^(1/a) = t^2
        return g(z / t ** 2) / t ** 2

    def Q(t, x):                       # int_0^x p_t(z) (x-z)^(-a) dz
        return quad(lambda z: p(t, z), 0, x, weight='alg', wvar=(0, -a), limit=200)[0]

    for x in (0.2, 0.5, 0.7):
        y = 1 - x
        val = quad(lambda t: p(t, y) * Q(t, x) + p(t, x) * Q(t, y), 0, np.inf, limit=200)[0]
        log(f'P4 a=1/2, x={x}: integral {val:.8f}  Lamperti {lamperti(x, a):.8f}  '
            f'rel diff {abs(val / lamperti(x, a) - 1):.1e}')
    log(f'\nTotal time {time.time() - t0:.0f} s')
    (HERE / 'lamperti_exact_output.txt').write_text('\n'.join(OUT) + '\n', encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()
