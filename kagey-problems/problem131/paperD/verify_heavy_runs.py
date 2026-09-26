"""Checks for Section 4 and Appendix C of Paper D (heavy-tailed runs).

Model. The steps form maximal runs of alternating direction. The first run has
length D and the later runs are i.i.d. copies of xi with P(xi >= k) = k^(-alpha).
Fresh start: D ~ xi. Stationary start: P(D = d) = d^(-alpha)/zeta(alpha). The
first direction is fair. C_n = P(A_n = n/2), E_n = P(A_n = n), R_n = E_n/C_n.

Method A (the two-renewal formula of Proposition 4.2). The + runs and the - runs
are 2 independent renewal processes, and the law of A_n is a sum over the number
of runs of products of renewal masses u_m and covering masses q_m. The
convolutions are done directly or by the fast Fourier transform.
Method B (spectral). The same products, but every factor is read off as a
Taylor coefficient of a power of the generating function, sampled on a circle
of radius r < 1. No convolution in time is used.
Method C (small n only). The first-run recursion with exact Hurwitz zeta tails,
and brute force over all 2^(n-1) run compositions in 30-digit arithmetic.

Run with python -B verify_heavy_runs.py, or add --full for the cells at
n = 10^5 by method A, the full crossover scan by method B and the grid search
for n*(1.60). Checks of numbers from the research notes that the paper no longer prints are
kept, labeled 'research notes, not printed'.
"""
import argparse
import math
import sys
import time

import mpmath as mp
import numpy as np
from scipy import fft as sfft
from scipy.special import zeta as hzeta

PHI = (1 + 5 ** 0.5) / 2
FAILS = []


def check(label, ok, detail):
    print(('  ok    ' if ok else '  FAIL  ') + label + ': ' + detail, flush=True)
    if not ok:
        FAILS.append(label)


def tol_of(printed):
    s = printed.lstrip('+-')
    mant = s.split('e')[0]
    exp10 = int(s.split('e')[1]) if 'e' in s else 0
    dec = len(mant.split('.')[1]) if '.' in mant else 0
    return 0.5 * 10.0 ** (exp10 - dec) * (1 + 1e-9) + 1e-15


def agree(label, printed, values, extra=''):
    target = float(printed)
    t = tol_of(printed)
    ok = all(abs(v - target) <= t for v in values.values())
    shown = ', '.join(f'{k} {v:.10g}' for k, v in values.items())
    check(label, ok, f'paper {printed}; {shown}{extra}')


# ---------------------------------------------------------------- method A

def kernels(alpha, n):
    k = np.arange(n + 1, dtype=float)
    T = np.zeros(n + 1)
    T[1:] = k[1:] ** (-alpha)                                   # P(xi >= k)
    p = np.zeros(n + 1)
    p[1:] = T[1:] * (-np.expm1(-alpha * np.log1p(1.0 / k[1:])))  # P(xi = k)
    return p, T


def edge(alpha, n, start):
    if start == 'fresh':
        return 0.5 * n ** (-float(alpha))
    return float(mp.zeta(alpha, n) / mp.zeta(alpha)) / 2


def center_all(alpha, nmax, tol=1e-14):
    """C_(2h) for every h <= nmax, fresh and stationary, by the two-renewal formula with FFT."""
    p, T = kernels(alpha, nmax)
    stat = alpha > 1
    mu = float(mp.zeta(alpha)) if stat else np.inf
    L = nmax + 1
    nfft = sfft.next_fast_len(2 * L)
    Fp, FT = sfft.rfft(p, nfft), sfft.rfft(T, nfft)
    FTT = sfft.rfft(sfft.irfft(FT * FT, nfft)[:L], nfft)

    def convs(u):
        Fu = sfft.rfft(u, nfft)
        return (sfft.irfft(Fp * Fu, nfft)[:L], sfft.irfft(FT * Fu, nfft)[:L],
                sfft.irfft(FTT * Fu, nfft)[:L] if stat else None)
    u0 = np.zeros(L)
    u0[0] = 1.0
    Zf, Zs = np.zeros(L), np.zeros(L)
    u_m, q_m, qD_next = convs(u0)            # u_1, q_1, and T*T*u_0 (divide by mu later)
    m = 1
    while True:
        u_next, q_next, qD_nn = convs(u_m)
        Zf += u_m * (q_m + q_next)
        if stat:
            Zs += u_m * qD_next / mu + q_m * q_m / mu
        if m >= nmax or u_m.sum() < tol:
            break
        u_m, q_m, qD_next = u_next, q_next, qD_nn
        m += 1
    return Zf, Zs


def dist_renewal(alpha, N, start):
    """Full symmetric law of A_N by the two-renewal formula, direct convolutions."""
    p, T = kernels(alpha, N)
    mu = float(mp.zeta(alpha)) if alpha > 1 else None
    L = N + 1
    TT = np.convolve(T, T)[:L]
    Pp = np.zeros(L)
    u0 = np.zeros(L)
    u0[0] = 1.0
    u_m = np.convolve(p, u0)[:L]
    q_m = np.convolve(T, u0)[:L]
    qD_next = np.convolve(TT, u0)[:L] / mu if start == 'stat' else None
    a = np.arange(1, N)
    b = N - a
    for m in range(1, N + 1):
        u_next = np.convolve(p, u_m)[:L]
        q_next = np.convolve(T, u_m)[:L]
        if start == 'fresh':
            Pp[a] += u_m[b] * q_next[a] + u_m[a] * q_m[b]
        else:
            Pp[a] += u_m[b] * qD_next[a] + (q_m[a] / mu) * q_m[b]
            qD_next = np.convolve(TT, u_m)[:L] / mu
        u_m, q_m = u_next, q_next
    Pp[N] = 2 * edge(alpha, N, start)
    return 0.5 * (Pp + Pp[::-1])


def near_center(alpha, N, start='fresh', tol=1e-14):
    """P(A_N = N/2 + d), d = -1, 0, 1, by the two-renewal formula with FFT."""
    n = N // 2
    p, T = kernels(alpha, N)
    L = N + 1
    nfft = sfft.next_fast_len(2 * L)
    Fp, FT = sfft.rfft(p, nfft), sfft.rfft(T, nfft)
    A = np.arange(n - 1, n + 2)
    B = N - A
    Pp = np.zeros(3)
    u0 = np.zeros(L)
    u0[0] = 1.0
    Fu = sfft.rfft(u0, nfft)
    u_m, q_m = sfft.irfft(Fp * Fu, nfft)[:L], sfft.irfft(FT * Fu, nfft)[:L]
    m = 1
    while True:
        Fu = sfft.rfft(u_m, nfft)
        u_next, q_next = sfft.irfft(Fp * Fu, nfft)[:L], sfft.irfft(FT * Fu, nfft)[:L]
        Pp += u_m[B] * q_next[A] + u_m[A] * q_m[B]
        if m >= N or u_m.sum() < tol:
            break
        u_m, q_m = u_next, q_next
        m += 1
    return 0.5 * (Pp + Pp[::-1])


# ---------------------------------------------------------------- method B (spectral)

def circle_values(alpha, M, r, L=3):
    """Phi(x) = sum_k P(xi=k) x^k and Psi(x) = sum_k P(xi>=k) x^k at x = r e^(2 pi i j/M)."""
    j = np.arange(1, L * M, dtype=float)
    damp = np.exp(j * math.log(r))
    cp, cT = np.zeros(L * M), np.zeros(L * M)
    cp[1:] = j ** (-alpha) * (-np.expm1(-alpha * np.log1p(1.0 / j))) * damp
    cT[1:] = j ** (-alpha) * damp
    Phi = (np.fft.ifft(cp.reshape(L, M).sum(axis=0)) * M)[:M // 2 + 1]
    Psi = (np.fft.ifft(cT.reshape(L, M).sum(axis=0)) * M)[:M // 2 + 1]
    return Phi, Psi


def extractor(n, M, r):
    k = np.arange(M // 2 + 1)
    w = np.full(M // 2 + 1, 2.0)
    w[0] = w[-1] = 1.0
    return w * np.exp(-2j * np.pi * ((n * k) % M) / M) * math.exp(-n * math.log(r)) / M


def law_point(alpha, a, b, starts, kappa=2.5, A=1e5, tol=1e-26):
    """P^+(A_N = a) with N = a + b, first run +, for each start, by coefficient extraction."""
    nref = max(a, b)
    M = 1 << int(math.ceil(math.log2(kappa * nref + 16)))
    r = A ** (-1.0 / nref)
    Phi, Psi = circle_values(alpha, M, r)
    mu = hzeta(alpha, 1) if alpha > 1 else None
    Ea, Eb = extractor(a, M, r), extractor(b, M, r)
    rows = [Phi * Eb, Psi * Eb]
    for st in starts:
        PhiD = Phi if st == 'fresh' else Psi / mu
        rows += [PhiD * Psi * Ea, PhiD * Ea]
    G = np.array(rows)
    v = np.ones(M // 2 + 1, dtype=complex)
    ph = Phi.copy()
    Z = np.zeros(len(starts))
    term_max, m_peak, small_run, m = 0.0, 1, 0, 0
    while m < max(a, b) + 1:
        m += 1
        vals = (G @ v).real
        terms = np.array([vals[0] * vals[2 + 2 * i] + vals[3 + 2 * i] * vals[1] for i in range(len(starts))])
        Z += terms
        tm = abs(terms).max()
        if tm > term_max:
            term_max, m_peak = tm, m
        if tm < 1e-22 * max(Z.max(), 1e-300) and m > 2 * m_peak + 50:
            small_run += 1
            if small_run > 400:
                break
        else:
            small_run = 0
        v *= ph
        if m % 32 == 0:
            keep = np.abs(v) > tol * abs(v[0])
            if keep.sum() < len(v):
                v, ph, G = v[keep], ph[keep], G[:, keep]
    return dict(zip(starts, Z))


def R_spectral(alpha, N, start='stat', **kw):
    return edge(alpha, N, start) / law_point(alpha, N // 2, N // 2, (start,), **kw)[start]


def all_centres_spectral(alpha, nmax, kappa=4.0, A=1e5):
    """C_(2h) for every h <= nmax (stationary start), spectral powers read off with FFTs."""
    M = 1 << int(math.ceil(math.log2(kappa * nmax + 16)))
    r = A ** (-1.0 / nmax)
    L = 3
    j = np.arange(1, L * M, dtype=float)
    damp = np.exp(j * math.log(r))
    cp, cT = np.zeros(L * M), np.zeros(L * M)
    cp[1:] = j ** (-alpha) * (-np.expm1(-alpha * np.log1p(1.0 / j))) * damp
    cT[1:] = j ** (-alpha) * damp
    Phi = np.fft.ifft(cp.reshape(L, M).sum(0)) * M
    Psi = np.fft.ifft(cT.reshape(L, M).sum(0)) * M
    mu = hzeta(alpha, 1)
    PhiD = Psi / mu
    n = np.arange(nmax + 1)
    unscale = np.exp(-n * math.log(r)) / M
    V = np.ones(M, dtype=complex)
    Z = np.zeros(nmax + 1)
    Am = nmax / mu
    for m in range(1, int(min(nmax + 1, Am + 12 * Am ** (1 / min(alpha, 2.0)) + 300)) + 1):
        f1 = np.fft.fft(V * (Phi + 1j * Psi))[:nmax + 1] * unscale      # u_m + i q_m
        f2 = np.fft.fft(V * PhiD * (Psi + 1j))[:nmax + 1] * unscale     # qD_(m+1) + i uD_m
        Z += f1.real * f2.real + f2.imag * f1.imag
        V *= Phi
    return Z


# ---------------------------------------------------------------- method C (small n)

def dist_firstrun(alpha, N, start):
    """Symmetric law of A_N by conditioning on the first run (exact Hurwitz zeta tails)."""
    k = np.arange(1, N + 2, dtype=float)
    surv = k ** (-alpha)
    pmf = surv * (-np.expm1(-alpha * np.log1p(1.0 / k)))
    F = [np.array([1.0])]
    for n in range(1, N + 1):
        f = np.zeros(n + 1)
        f[n] += surv[n - 1]
        for j in range(1, n):
            f[j:n + 1] += pmf[j - 1] * F[n - j][::-1]
        F.append(f)
    if start == 'fresh':
        H = F[N].copy()
    else:
        mu = float(mp.zeta(alpha))
        H = np.zeros(N + 1)
        H[N] += float(mp.zeta(alpha, N)) / mu
        for j in range(1, N):
            H[j:N + 1] += (surv[j - 1] / mu) * F[N - j][::-1]
    return 0.5 * (H + H[::-1])


def brute(alpha, N, start):
    """Sum over all run compositions of N, in 30-digit arithmetic."""
    mp.mp.dps = 30
    a = mp.mpf(alpha)
    surv = lambda k: mp.mpf(k) ** (-a)
    pmf = lambda k: surv(k) - surv(k + 1)
    mu = mp.zeta(a) if alpha > 1 else None
    first = (lambda k: surv(k) / mu) if start == 'stat' else pmf
    first_tail = (lambda k: mp.zeta(a, k) / mu) if start == 'stat' else surv
    P = [mp.mpf(0)] * (N + 1)
    for mask in range(1 << (N - 1)):
        runs, last = [], 0
        for i in range(1, N):
            if mask >> (i - 1) & 1:
                runs.append(i - last)
                last = i
        runs.append(N - last)
        if len(runs) == 1:
            w = first_tail(N)
        else:
            w = first(runs[0])
            for r in runs[1:-1]:
                w *= pmf(r)
            w *= surv(runs[-1])
        plus = sum(runs[0::2])
        P[plus] += w / 2
        P[N - plus] += w / 2
    return P


# ---------------------------------------------------------------- constants

def consts(a):
    a = mp.mpf(a)
    mu = mp.zeta(a)
    K = mp.gamma(2 - a) / (a - 1)
    c = abs(mp.cos(mp.pi * a / 2))
    C = mp.pi * (K * c) ** (1 / a) / (4 * (a - 1) * mp.gamma(1 + 1 / a) * mu ** (1 + 1 / a))
    return dict(e=1 - a + 1 / a, mu=mu, K=K, C=C, Cfr=(a - 1) * mu * C)


def C_by_quadrature(a):
    """Second route: C = 1/(4(a-1) mu I (2 mu)^(1/a)), with I = int g^2 = (1/pi) int_0^oo e^(-sigma t^a) dt
    computed by quadrature, sigma = 2 K |cos(pi a/2)| and K = -Gamma(1-a)."""
    a = mp.mpf(a)
    mu = mp.zeta(a)
    K = -mp.gamma(1 - a)
    sig = 2 * K * abs(mp.cos(mp.pi * a / 2))
    I = mp.quad(lambda t: mp.exp(-sig * t ** a), [0, 1, mp.inf]) / mp.pi
    return 1 / (4 * (a - 1) * mu * I * (2 * mu) ** (1 / a))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--full', action='store_true', help='also run the heavy cells')
    args = ap.parse_args()
    T0 = time.time()
    print('Paper D, Section 4: heavy-tailed runs' + (' (full run)' if args.full else ' (quick run)'))
    mp.mp.dps = 30
    alphas = [('1.3', 1.3), ('1.5', 1.5), ('phi', PHI), ('5/3', 5 / 3), ('1.7', 1.7), ('1.9', 1.9)]

    # ------------------------------------------------ small n: 3 engines
    print('\nThree engines on every bin for n <= 14 (Section 5)', flush=True)
    t0 = time.time()
    worst, totals = 0.0, 0.0
    laws = [(a, s) for a in (1.3, 1.5, PHI, 1.9, 2.5) for s in ('stat', 'fresh')] + [(0.4, 'fresh'), (0.8, 'fresh')]
    for alpha, start in laws:
        for N in (2, 3, 4, 5, 8, 11, 14):
            if alpha < 1 and N not in (4, 9, 14):
                continue
            B = brute(alpha, N, start)
            totals = max(totals, float(abs(mp.fsum(B) - 1)))
            Pe = dist_renewal(alpha, N, start)
            worst = max(worst, max(abs(float(B[i]) - Pe[i]) / float(B[i]) for i in range(N + 1)))
            if alpha > 1:
                Pr = dist_firstrun(alpha, N, start)
                worst = max(worst, max(abs(float(B[i]) - Pr[i]) / float(B[i]) for i in range(N + 1)))
    check('two-renewal formula, first-run recursion and brute force agree, all bins, n <= 14',
          worst <= 1e-15 and totals < 1e-20,
          f'largest relative difference {worst:.1e} (paper 7e-16); brute-force totals differ from 1 by at most {totals:.0e} (30 digits)'
          f'  [{time.time() - t0:.0f}s]')

    # ------------------------------------------------ Proposition 4.1
    print('\nProposition 4.1 (the end)', flush=True)
    ok, worst_theta = True, (1.0, 0.0)
    for alpha in (1.1, 1.3, 1.5, PHI, 1.9, 2.5, 3.5):
        for n in (1, 2, 5, 10, 100, 1000, 10 ** 5):
            En = edge(alpha, n, 'stat')
            lead = n ** (1 - alpha) / (2 * (alpha - 1) * float(mp.zeta(alpha)))
            theta = (En / lead - 1) * n / (alpha - 1)
            ok &= -1e-9 <= theta <= 1 + 1e-9
            worst_theta = (min(worst_theta[0], theta), max(worst_theta[1], theta))
    for alpha, start in ((1.5, 'stat'), (1.5, 'fresh'), (PHI, 'stat')):
        for N in (5, 11):
            ok &= abs(float(brute(alpha, N, start)[N]) / edge(alpha, N, start) - 1) < 1e-14
    check('E_n = P(D >= n)/2, and theta_n in [0, 1] in the stationary expansion', ok,
          f'theta_n ranges over [{worst_theta[0]:.4f}, {worst_theta[1]:.4f}] on the tested cells')

    # ------------------------------------------------ constants of Corollary 4.5
    print('\nConstants of Corollary 4.5 (Table 2)', flush=True)
    table_consts = {'1.3': ('+0.469231', '0.422717', '0.498631'), '1.5': ('+0.166667', '0.647971', '0.846371'),
                    'phi': ('0', '0.776132', '1.073675'), '5/3': (None, '0.835101', '1.182237'),
                    '1.7': ('-0.111765', '0.880046', '1.265508'), '1.9': ('-0.373684', '1.438986', '2.266075')}
    for name, a in alphas:
        aa = (1 + mp.sqrt(5)) / 2 if name == 'phi' else (mp.mpf(5) / 3 if name == '5/3' else mp.mpf(name))
        d = consts(aa)
        ep, Cp, Cfp = table_consts[name]
        if name == 'phi':
            check('e(phi) = 0', abs(d['e']) < 1e-25, mp.nstr(d['e'], 5))
        elif ep is not None:
            agree(f'e({name})', ep, {'formula': float(d['e'])})
        else:
            check('e(5/3) = -1/15', abs(d['e'] + mp.mpf(1) / 15) < 1e-25, mp.nstr(d['e'], 12))
        Cq = C_by_quadrature(aa)
        agree(f'C({name})', Cp, {'closed form': float(d['C']), 'quadrature': float(Cq)})
        agree(f'C_fr({name})', Cfp, {'formula': float(d['Cfr']), 'quadrature': float((aa - 1) * mp.zeta(aa) * Cq)})
    ph = (1 + mp.sqrt(5)) / 2
    d = consts(ph)
    Cclosed = mp.pi * ph * (ph * mp.gamma(ph ** -2) * abs(mp.cos(mp.pi * ph / 2))) ** (1 / ph) / (
        4 * mp.gamma(ph) * mp.zeta(ph) ** ph)
    agree('C(phi), golden-ratio closed form', '0.7761317206', {'general formula': float(d['C']), 'closed form': float(Cclosed)})
    agree('1/C(phi)', '1.2884', {'formula': float(1 / d['C'])})
    agree('|log C(phi)| (research notes, not printed)', '0.25343', {'formula': float(abs(mp.log(d['C'])))})
    agree('C(5/3) in Remark 4.7', '0.8351', {'formula': float(consts(mp.mpf(5) / 3)['C'])})

    # ------------------------------------------------ Table 2: exact R_n, stationary start
    print('\nExact R_n for the stationary start (Table 2)', flush=True)
    tab = {'1.3': ('17.7593', '1.3180', '38.7537', '1.2171', '106.149', '1.1317'),
           '1.5': ('2.14409', '0.9675', '2.9528', '0.9818', '4.37642', '0.9914'),
           'phi': ('0.661763', '0.8526', '0.697331', '0.8985', '0.727689', '0.9376'),
           '5/3': ('0.411815', '0.8064', '0.389307', '0.8614', '0.352822', '0.9102'),
           '1.7': ('0.298369', '0.7733', '0.262005', '0.8334', '0.215839', '0.8881'),
           '1.9': ('0.0449706', '0.4923', '0.0256505', '0.5569', '0.0121612', '0.6242')}
    R5_3 = {}
    for name, a in alphas:
        t0 = time.time()
        d = consts(a)
        C, e = float(d['C']), float(d['e'])
        nmax = 50000 if args.full else 5000
        Zf, Zs = center_all(a, nmax)
        cells = (1600, 10 ** 4, 10 ** 5)
        for i, N in enumerate(cells):
            vals = {}
            if N // 2 <= nmax:
                vals['A'] = edge(a, N, 'stat') / Zs[N // 2]
            vals['B'] = R_spectral(a, N)
            agree(f'R_{N} for alpha = {name}', tab[name][2 * i], vals)
            agree(f'R_{N}/(C n^e) for alpha = {name}', tab[name][2 * i + 1], {k: v / (C * N ** e) for k, v in vals.items()})
            if name == '5/3':
                R5_3[N] = vals['B']
        print(f'        [alpha = {name}: {time.time() - t0:.1f}s]', flush=True)
        if name == 'phi':
            r5 = R_spectral(a, 10 ** 5)
            agree('R_(10^5) at alpha = phi (Table 2 prints 0.727689)', '0.72769', {'B': r5})
            agree('R_(10^5)/C(phi) (text after Corollary 4.5)', '0.938', {'B': r5 / C})
    if not args.full:
        print('  skip  method A at n = 10^5 (run with --full); method B covers these cells')

    # ------------------------------------------------ Remark 4.7: alpha = 5/3
    print('\nRemark 4.7 (alpha = 5/3; the values here are research notes, not printed, except Table 2)', flush=True)
    a = 5 / 3
    Zf, Zs = center_all(a, 200)
    RA = {N: edge(a, N, 'stat') / Zs[N // 2] for N in range(20, 401, 2)}
    ZB = all_centres_spectral(a, 200)
    RB = {N: edge(a, N, 'stat') / ZB[N // 2] for N in range(20, 401, 2)}
    dev = max(abs(RA[N] / RB[N] - 1) for N in RA)
    peakA = max(RA, key=RA.get)
    up = all(RA[N + 2] > RA[N] for N in range(20, peakA, 2))
    down = all(RA[N + 2] < RA[N] for N in range(peakA, 400, 2))
    check('over even n in [20, 400], R_n rises to its maximum at n = 150 and then falls (research notes, not printed)',
          peakA == max(RB, key=RB.get) == 150 and up and down,
          f'argmax A {peakA}, B {max(RB, key=RB.get)}; A and B agree to {dev:.1e}')
    agree('R_150 at alpha = 5/3 (research notes, not printed)', '0.42419', {'A': RA[150], 'B': RB[150]})
    gridN = [400, 800, 1600, 3200, 6400, 10 ** 4, 2 * 10 ** 4, 5 * 10 ** 4, 10 ** 5]
    Rg = [R_spectral(a, N) for N in gridN]
    check('R_n decreases on the grid 400, 800, ..., 10^5 (research notes, not printed)', all(x > y for x, y in zip(Rg, Rg[1:])),
          ', '.join(f'{v:.5f}' for v in Rg))
    agree('R_n/(C(5/3) n^(-1/15)) at n = 10^5 (Table 2 prints 0.9102)', '0.910', {'B': Rg[-1] / (float(consts(a)['C']) * 1e5 ** (-1 / 15))})

    # ------------------------------------------------ Remark 4.7: crossover sizes
    print('\nCrossover sizes n*(alpha) for the stationary start (Remark 4.7)', flush=True)
    nstar_p = {1.5: 26, 1.55: 192, 1.58: 2596, 1.59: 14530}
    lead = {1.5: '13.5', 1.55: '41.8', 1.58: '350', 1.59: '1959', 1.60: '7.38e4'}
    found = {}
    for a, ns in nstar_p.items():
        t0 = time.time()
        Zf, Zs = center_all(a, 15000)
        mu = mp.zeta(a)
        Ns = np.arange(10, 30001, 2)
        z = mp.zeta(a, int(Ns[0]))
        Ed = np.empty(len(Ns))
        for i, N in enumerate(Ns):                   # zeta(a, N+2) = zeta(a, N) - N^-a - (N+1)^-a
            if i:
                z -= mp.mpf(int(Ns[i - 1])) ** (-a) + mp.mpf(int(Ns[i - 1]) + 1) ** (-a)
            Ed[i] = float(z / (2 * mu))
        R = Ed / Zs[Ns // 2]
        s = np.sign(R - 1)
        ch = [int(Ns[i]) for i in range(1, len(s)) if s[i] != s[i - 1]]
        rb = (R_spectral(a, ns - 2), R_spectral(a, ns))
        ok = ch == [ns] and rb[0] < 1 < rb[1]
        extra = ''
        if args.full:
            ZB = all_centres_spectral(a, 15000)
            RBall = Ed / ZB[Ns // 2]
            sB = np.sign(RBall - 1)
            chB = [int(Ns[i]) for i in range(1, len(sB)) if sB[i] != sB[i - 1]]
            ok &= chB == [ns]
            extra = f'; B over every even n: {chB}'
        found[a] = ns
        check(f'n*({a}): one sign change of R_n - 1 on even n in [10, 30000]', ok,
              f'paper {ns}; A sign changes at {ch}; B: R_(n*-2) - 1 = {rb[0] - 1:+.2e}, R_(n*) - 1 = {rb[1] - 1:+.2e}'
              f'{extra}  [{time.time() - t0:.0f}s]')
    t0 = time.time()
    r1, r2 = R_spectral(1.60, 372658), R_spectral(1.60, 372660)
    r1b, r2b = R_spectral(1.60, 372658, kappa=4.0, A=1e3), R_spectral(1.60, 372660, kappa=4.0, A=1e3)
    check('n*(1.60) = 372660: R_n - 1 changes sign between 372658 and 372660', r1 < 1 < r2 and r1b < 1 < r2b,
          f'R - 1 = {r1 - 1:+.3e}, {r2 - 1:+.3e} (other circle parameters {r1b - 1:+.3e}, {r2b - 1:+.3e})'
          f'  [{time.time() - t0:.0f}s]')
    if args.full:
        t0 = time.time()
        grid = sorted(set(int(2 * round(v / 2)) for v in np.geomspace(3e4, 4.2e5, 30)))
        vals = [R_spectral(1.60, N) for N in grid]
        s = np.sign(np.array(vals) - 1)
        chg = [i for i in range(len(s) - 1) if s[i] != s[i + 1]]
        lo, hi = grid[chg[0]], grid[chg[0] + 1]
        while hi - lo > 2:
            mid = 2 * ((lo + hi) // 4)
            if mid <= lo:
                mid = lo + 2
            if R_spectral(1.60, mid) > 1:
                hi = mid
            else:
                lo = mid
        check('n*(1.60) by a 30-point grid on [3e4, 4.2e5] and bisection (a research check not quoted in the paper)', len(chg) == 1 and hi == 372660,
              f'{hi}  [{time.time() - t0:.0f}s]')
    found[1.60] = 372660
    for a, ns in found.items():
        d = consts(a)
        L0 = float(d['C'] ** (-1 / d['e']))
        agree(f'leading-order crossover C(alpha)^(-1/e(alpha)) at alpha = {a} (research notes, not printed)', lead[a], {'formula': L0},
              f'; n*/leading = {ns / L0:.2f}')
    facs = [ns / float(consts(a)['C'] ** (-1 / consts(a)['e'])) for a, ns in found.items()]
    check('the leading order underestimates n* by factors 1.9 to 7.4 (research notes, not printed)', round(min(facs), 1) == 1.9 and round(max(facs), 1) == 7.4,
          f'factors {", ".join(f"{f:.2f}" for f in facs)}')
    slope = float(abs(mp.log(consts(PHI)['C'])) / (1 + PHI ** -2))
    agree('|log C(phi)|/|e\'(phi)| in the heuristic for log n* (Remark 4.7)', '0.1834', {'formula': slope})
    offs = [math.log(ns) - slope / (PHI - a) for a, ns in found.items()]
    check('log n* - 0.1834/(phi - alpha) lies between 1.7 and 3.0 (research notes, not printed)', round(min(offs), 1) >= 1.7 and round(max(offs), 1) <= 3.0,
          ', '.join(f'{o:.2f}' for o in offs))

    # ------------------------------------------------ alpha <= 1, fresh start (Remark 4.6, Table 3)
    print('\nFresh start with alpha <= 1 (Remark 4.6, Table 3)', flush=True)
    ac1 = mp.findroot(lambda a: a - mp.cos(mp.pi * a / 2), 0.6)

    def lamperti(y, a):
        return (mp.sin(mp.pi * a) / mp.pi * y ** (a - 1) * (1 - y) ** (a - 1)
                / (y ** (2 * a) + 2 * y ** a * (1 - y) ** a * mp.cos(mp.pi * a) + (1 - y) ** (2 * a)))
    ac2 = mp.findroot(lambda a: mp.diff(lambda y: lamperti(y, a), mp.mpf(1) / 2, 2), 0.6)
    agree('alpha_c (research notes, not printed)', '0.5946116441', {'alpha = cos(pi alpha/2)': float(ac1), "root of l_alpha''(1/2)": float(ac2)})
    worst = max(abs(lamperti(mp.mpf(1) / 2, mp.mpf(a)) / (2 / mp.pi * mp.tan(mp.pi * a / 2)) - 1) for a in (0.3, 0.5, 0.7, 0.9))
    check('l_alpha(1/2) = (2/pi) tan(pi alpha/2) (Table 3)', worst < 1e-25, f'largest relative difference {mp.nstr(worst, 2)}')
    for a, kind, printed in ((0.58, 'MIN', '4e-9'), (0.61, 'MAX', '-2e-9')):
        t0 = time.time()
        PA = near_center(a, 16000)
        n = 8000
        # The relative second difference is only a few times 1e-9. The spectral method multiplies
        # rounding errors by r^(-n) = A, so here we take the circle with A = 1e3 (aliasing error
        # A^(-kappa) = 1e-12) instead of the default A = 1e5.
        kw = dict(kappa=4.0, A=1e3)
        Z0 = law_point(a, n, n, ('fresh',), **kw)['fresh']
        Zp = law_point(a, n + 1, n - 1, ('fresh',), **kw)['fresh']
        Zm = law_point(a, n - 1, n + 1, ('fresh',), **kw)['fresh']
        PB = np.array([0.5 * (Zp + Zm), Z0, 0.5 * (Zp + Zm)])
        sdA = (PA[0] + PA[2] - 2 * PA[1]) / PA[1]
        sdB = (PB[0] + PB[2] - 2 * PB[1]) / PB[1]
        is_kind = (sdA > 0 and sdB > 0) if kind == 'MIN' else (sdA < 0 and sdB < 0)
        check(f'center bin at n = 16000 is a local {kind} for alpha = {a} (research notes, not printed)',
              is_kind and abs(sdA - float(printed)) < 0.5 * abs(float(printed)) and abs(sdA / sdB - 1) < 1e-2,
              f'relative second difference A {sdA:+.3e}, B {sdB:+.3e} (notes about {printed})  [{time.time() - t0:.1f}s]')
    agree('leading-order crossover (4 tan(pi alpha/2)/pi)^(1/(1-alpha)) at alpha = 0.7 (research notes, not printed)', '21',
          {'formula': (4 * math.tan(0.35 * math.pi) / math.pi) ** (1 / 0.3)})
    agree('the same at alpha = 0.9 (research notes, not printed)', '1.1e9', {'formula': (4 * math.tan(0.45 * math.pi) / math.pi) ** (1 / 0.1)})
    Zf, _ = center_all(0.9, 8000)
    agree('R_16000 at alpha = 0.9, fresh start (research notes, not printed)', '0.59',
          {'A': edge(0.9, 16000, 'fresh') / Zf[8000], 'B': R_spectral(0.9, 16000, 'fresh')})
    from scipy.optimize import brentq
    nmax = 50000 if args.full else 5000
    Zf, _ = center_all(1.0, nmax)
    for N, printed in ((1600, '0.796'), (10 ** 4, '0.850'), (10 ** 5, '0.886')):
        h = N / 2
        mh = brentq(lambda y: y * (float(mp.harmonic(y + 1)) - 1) - h, 1.0, h)
        heur = math.pi ** 2 * mh / (8 * h)
        vals = {'B': R_spectral(1.0, N, 'fresh') / heur}
        if N // 2 <= nmax:
            vals['A'] = edge(1.0, N, 'fresh') / Zf[N // 2] / heur
        agree(f'alpha = 1: R_n divided by the heuristic pi^2 m_h/(8h), n = {N} (research notes, not printed)', printed, vals)

    print(f'\nSection 4 checks done in {time.time() - T0:.0f}s: '
          + ('all passed.' if not FAILS else f'{len(FAILS)} FAILED: ' + '; '.join(FAILS)))
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
