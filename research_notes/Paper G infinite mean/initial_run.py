"""Paper G: the initial run in the infinite-mean regime (Theorem 3 and Corollary 3.4 of 01_report.md).

Run:  py -I initial_run.py

Symmetric zeta laws f(n) = n^(-a-1)/zeta(a+1) with a = 0.5. The law for an arbitrary initial run
(sign s, length d) is assembled from the first-run decomposition of Paper F,
    P_N(k) = Q+(N) 1{k=N} + Q-(N) 1{k=0} + sum_{d<N} nu+(d) F-_{N-d}(k-d) + sum_{d<N} nu-(d) F+_{N-d}(k),
with the fresh laws computed as in lamperti_exact.py (F-_n(i) = F+_n(n-i) by symmetry).

Two initial runs:
 (R) fixed law: sign fair, nu(d) proportional to d^(-1.2); n nu(n) -> 0, so the theorem predicts
     the local Lamperti law, N P_N(k) -> L(k/N).
 (S) scale-N law (aging type): sign fair, D uniform on {1, ..., N/2}. The corollary predicts
     N P_N(k) -> int_0^{min(x,1/2)} L((x-z)/(1-z))/(1-z) dz + int_0^{min(1-x,1/2)} L(x/(1-z))/(1-z) dz.
"""
import hashlib
import sys
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.special import zeta

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from lamperti_exact import laws, arrays, fresh_plus, lamperti  # noqa: E402

OUT = []


def log(s=""):
    print(s, flush=True)
    OUT.append(s)


def main():
    a = 0.5
    log('# script: initial_run.py')
    log('# sha256: ' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    nmax = 2000
    f, T = laws(a, nmax)
    _, A, B = arrays(f, nmax)
    xs = (0.3, 0.5, 0.7)
    for N in (500, 1000, 2000):
        Fp = {n: fresh_plus(A, B, T, n) for n in range(1, N + 1)}   # Fp[n][i] = F+_n(i)

        def Fm(n, i):                                               # F-_n(i) = F+_n(n-i)
            return Fp[n][n - i] if 0 <= i <= n else 0.0

        def law(nup, num, Qp, Qm):
            P = np.zeros(N + 1)
            for k in range(N + 1):
                s = 0.0
                for d in range(1, N):
                    if nup[d] and k - d >= 0:
                        s += nup[d] * Fm(N - d, k - d)
                    if num[d] and k <= N - d:
                        s += num[d] * Fp[N - d][k]
                P[k] = s
            P[N] += Qp
            P[0] += Qm
            return P

        d = np.arange(N + 1, dtype=float)
        # (R)
        w = np.zeros(N + 1); w[1:] = d[1:] ** -1.2 / zeta(1.2)
        Q = 1 - w[1:N].sum()                                        # P(D >= N)
        PR = law(w / 2, w / 2, Q / 2, Q / 2)
        # (S)
        h = N // 2
        v = np.zeros(N + 1); v[1:h + 1] = 1.0 / h
        PS = law(v / 2, v / 2, 0.0, 0.0)
        pred = []
        for x in xs:
            i1 = quad(lambda z: lamperti((x - z) / (1 - z), a) / (1 - z), 0, min(x, 0.5), limit=200)[0]
            i2 = quad(lambda z: lamperti(x / (1 - z), a) / (1 - z), 0, min(1 - x, 0.5), limit=200)[0]
            pred.append(i1 + i2)
        log(f'N={N}: (R) N P_N/L at x={xs}: '
            + ' '.join(f'{N * PR[round(x * N)] / lamperti(x, a):.4f}' for x in xs)
            + f'  mass {PR.sum():.10f}')
        log(f'       (S) N P_N at x={xs}: '
            + ' '.join(f'{N * PS[round(x * N)]:.4f}' for x in xs)
            + '   predicted ' + ' '.join(f'{p:.4f}' for p in pred)
            + f'   (fresh L: ' + ' '.join(f'{lamperti(x, a):.4f}' for x in xs) + f')  mass {PS.sum():.10f}')
    (HERE / 'initial_run_output.txt').write_text('\n'.join(OUT) + '\n', encoding='utf-8', newline='\n')


if __name__ == '__main__':
    main()
