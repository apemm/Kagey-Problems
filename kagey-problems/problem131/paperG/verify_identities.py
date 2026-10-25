"""The exact identities of Section sec:setting against a sum over all sign strings, N <= 12.

Laws: plus runs f_+(n) proportional to n^(-a-1), minus runs f_-(n) proportional to (n+3)^(-a-1),
for a = 0.3 and a = 0.7 (two different laws, so the two signs are not exchangeable).
  1. The run-sum form eq:run-sum (arrays A and B of lamperti_law.py) for a fresh plus start.
  2. The fresh-plus identity prop:fresh-identity, written with the kernels u_m and q_m.
  3. The first-run decomposition prop:first-run for a general initial run, with the fresh laws of
     both signs computed by eq:run-sum.
  4. The final-run identity prop:final-run (eq:final-explicit) for a fresh plus start.
Each check passes if the largest absolute difference is below 1e-14.

Run from the paper folder:  py -I verify_identities.py
Output: data/verify_identities_output.txt (with the sha256 of this script and the date).
Exit status 1 if any check fails.
"""
import importlib.util
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("lamperti_law", HERE / "lamperti_law.py")
lw = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lw)

R = lw.Report(__file__)
NMAX = 12
TOL = 1e-14


def kernels(f, T, nmax):
    U = lw.convolution_powers(f, nmax)
    q = np.zeros((nmax + 2, nmax + 1))          # q[m, k] = sum_{r<k} u_{m-1}(r) T(k-r)
    for m in range(1, nmax + 2):
        for k in range(1, nmax + 1):
            q[m, k] = sum(U[m - 1, r] * T[k - r] for r in range(k)) if m - 1 <= nmax else 0.0
    return U, q


def fresh_identity(N, Up, qp, Um, qm, Tp):
    P = np.zeros(N + 1)
    P[N] = Tp[N]
    for k in range(1, N):
        j = N - k
        P[k] = sum(Um[m, j] * qp[m + 1, k] + Up[m, k] * qm[m, j] for m in range(1, N + 1))
    return P


def final_run(N, Up, Um, Tp, Tm):
    P = np.zeros(N + 1)
    for j in range(N):
        s = 0.0
        for r in range(j + 1):
            s += Um[r, j] * sum(Up[r, x] * Tp[N - j - x] for x in range(N - j))
        for m in range(1, j + 1):
            s += Tm[m] * sum(Um[r, j - m] * Up[r + 1, N - j] for r in range(j - m + 1))
        P[N - j] = s
    return P


def main():
    t0 = time.time()
    R.log("verify_identities.py: exact identities against all sign strings, N <= 12")
    worst = {1: 0.0, 2: 0.0, 3: 0.0, 4: 0.0}
    for a in (0.3, 0.7):
        fp, Tp = lw.zeta_law(a, NMAX + 2)
        fm, Tm = lw.zeta_law(a, NMAX + 2, shift=3)
        Up, qp = kernels(fp, Tp, NMAX)
        Um, qm = kernels(fm, Tm, NMAX)
        A, B = lw.arrays(Up, Um)                # fresh plus
        A2, B2 = lw.arrays(Um, Up)              # fresh minus, signs exchanged
        # a general initial run: sign + with probability 0.6 and length law proportional to
        # d^(-1.5) (1.2 + sin d), sign - with probability 0.4 and length law proportional to d^(-1.2),
        # both on 1 <= d < NMAX + 30
        d = np.arange(1, NMAX + 30, dtype=float)
        wp = d ** -1.5 * (1.2 + np.sin(d))
        wm = d ** -1.2
        nup = np.concatenate(([0.0], 0.6 * wp / wp.sum()))
        num = np.concatenate(([0.0], 0.4 * wm / wm.sum()))
        for N in range(1, NMAX + 1):
            bp = lw.brute(N, fp, Tp, fm, Tm)
            P1 = lw.fresh_plus(A, B, Tp, Tm, N)
            worst[1] = max(worst[1], np.max(np.abs(P1 - bp)))
            P2 = fresh_identity(N, Up, qp, Um, qm, Tp)
            worst[2] = max(worst[2], np.max(np.abs(P2 - bp)))
            P4 = final_run(N, Up, Um, Tp, Tm)
            worst[4] = max(worst[4], np.max(np.abs(P4[1:] - bp[1:])))
            Qp = 0.6 - nup[1:N].sum()
            Qm = 0.4 - num[1:N].sum()
            bg = lw.brute(N, fp, Tp, fm, Tm, nup, num, Qp, Qm)
            P3 = np.zeros(N + 1)
            P3[N] += Qp
            P3[0] += Qm
            for d in range(1, N):
                Fp = lw.fresh_plus(A, B, Tp, Tm, N - d)            # F+_{N-d}
                Fm = lw.fresh_plus(A2, B2, Tm, Tp, N - d)[::-1]    # F-_{N-d}(i) = count of minus steps N-d-i
                for k in range(N + 1):
                    if 0 <= k - d <= N - d:
                        P3[k] += nup[d] * Fm[k - d]
                    if k <= N - d:
                        P3[k] += num[d] * Fp[k]
            worst[3] = max(worst[3], np.max(np.abs(P3 - bg)))
            if N == NMAX:
                R.log(f"   a = {a}, N = {N}: total mass fresh {bp.sum():.15f}, general {bg.sum():.15f}")
    R.check("1. eq:run-sum equals the sum over sign strings", worst[1] < TOL, f"max diff {worst[1]:.1e}")
    R.check("2. prop:fresh-identity equals the sum over sign strings", worst[2] < TOL, f"max diff {worst[2]:.1e}")
    R.check("3. prop:first-run equals the sum over sign strings for a general initial run", worst[3] < TOL,
            f"max diff {worst[3]:.1e}")
    R.check("4. prop:final-run equals the sum over sign strings", worst[4] < TOL, f"max diff {worst[4]:.1e}")
    sys.exit(R.write(time.time() - t0))


if __name__ == "__main__":
    main()
