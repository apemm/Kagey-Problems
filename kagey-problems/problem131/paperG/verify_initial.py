"""The numbers of Section sec:verify on the initial run (Theorem thm:initial and the mixture of Theorem thm:mixture).

Model: the zeta law f(n) = n^(-a-1)/zeta(a+1) for both signs, a = 1/2. The law for an initial run is
assembled from prop:first-run with the fresh laws computed by eq:run-sum (F-_n(i) = F+_n(n-i) by
symmetry).
  (R) A fixed initial run: sign + or - with probability 1/2, length law nu(d) = d^(-1.2)/zeta(1.2).
      Here n nu(n) -> 0, so thm:initial(c) gives the local Lamperti law.
  1. N P_N(N/2)/L(1/2) is 0.815, 0.836, 0.855 at N = 500, 1000, 2000, and it increases.
  2. The gap 1 - N P_N(N/2)/L(1/2) decays like P(D >= N), of order N^(-0.2). The product
     (1 - ratio) N^0.2 changes by less than 5 percent from N = 500 to N = 2000. The defect terms
     D+_N(N/2) + D-_N(N/2) of thm:initial(a) are printed, and they decrease.
  3. The end layer thm:initial(f): P_N(N-j)/(T(N) kappa_+(j)) for j = 1, 2, 3 moves toward 1 from
     N = 500 to N = 2000.
  (S) A scale-N initial run (Theorem thm:mixture): sign fair, D uniform on {1, ..., N/2}.
  4. N P_N(k) at x = 0.3, 0.5 is 0.898, 1.325 at N = 500 and 0.884, 1.299 at N = 2000, and it moves
     toward the values 0.8694, 1.2732 of the mixture of Theorem thm:mixture. At x = 1/2 that value is
     4/pi = 2 L(1/2).
  5. The total mass is 1 to 10 digits.

Run from the paper folder:  py -I verify_initial.py
Output: data/verify_initial_output.txt (with the sha256 of this script and the date).
Exit status 1 if any check fails.
"""
import importlib.util
import sys
import time
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.special import zeta

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("lamperti_law", HERE / "lamperti_law.py")
lw = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lw)

R = lw.Report(__file__)
A_ = 0.5


def main():
    t0 = time.time()
    a = A_
    nmax = 2000
    f, T = lw.zeta_law(a, nmax)
    U = lw.convolution_powers(f, nmax)
    A, B = lw.arrays(U, U)
    u = U.sum(axis=0)
    del U
    R.log("verify_initial.py: symmetric zeta law, a = 1/2")
    ratios, defects, endr, S3, S5, masses = [], [], [], [], [], []
    xs = (0.3, 0.5)
    pred = []
    for x in xs:
        i1 = quad(lambda z: lw.lamperti((x - z) / (1 - z), a) / (1 - z), 0, min(x, 0.5), limit=200)[0]
        i2 = quad(lambda z: lw.lamperti(x / (1 - z), a) / (1 - z), 0, min(1 - x, 0.5), limit=200)[0]
        pred.append(i1 + i2)
    for N in (500, 1000, 2000):
        Fp = [lw.fresh_plus(A, B, T, T, n) if n >= 1 else np.array([1.0]) for n in range(N + 1)]

        def law(nup, num, Qp, Qm):
            P = np.zeros(N + 1)
            for d in range(1, N):
                n = N - d
                if nup[d]:
                    P[d:] += nup[d] * Fp[n][::-1]          # F-_n(i) = F+_n(n-i), at k = d + i
                if num[d]:
                    P[:n + 1] += num[d] * Fp[n]
            P[N] += Qp
            P[0] += Qm
            return P

        d = np.arange(N + 1, dtype=float)
        w = np.zeros(N + 1)
        w[1:] = d[1:] ** -1.2 / zeta(1.2)
        Q = 1 - w[1:N].sum()
        PR = law(w / 2, w / 2, Q / 2, Q / 2)
        masses.append(abs(PR.sum() - 1))
        k = N // 2
        ratio = N * PR[k] / lw.lamperti(0.5, a)
        Dp = N * sum(w[dd] / 2 * Fp[N - dd][N - dd - (k - dd)] for dd in range((k + 1) // 2, k + 1))
        Dm = N * sum(w[dd] / 2 * Fp[N - dd][k] for dd in range((N - k + 1) // 2, N - k + 1))
        ratios.append(ratio)
        defects.append(Dp + Dm)
        kap = [0.5 * u[j] + sum(w[dd] / 2 * u[j - dd] for dd in range(1, j + 1)) for j in range(4)]
        er = [PR[N - j] / (T[N] * kap[j]) for j in (1, 2, 3)]
        endr.append(er)
        R.log(f"   (R) N={N}: N P_N(N/2)/L(1/2) = {ratio:.4f}, D+ + D- = {Dp + Dm:.4f}, "
              f"(1 - ratio) N^0.2 = {(1 - ratio) * N ** 0.2:.4f}, "
              f"P_N(N-j)/(T(N) kappa(j)), j=1,2,3: " + " ".join(f"{v:.4f}" for v in er) + f", mass {PR.sum():.12f}")
        h = N // 2
        v = np.zeros(N + 1)
        v[1:h + 1] = 1.0 / h
        PS = law(v / 2, v / 2, 0.0, 0.0)
        masses.append(abs(PS.sum() - 1))
        vals = [N * PS[round(x * N)] for x in xs]
        S3.append(vals[0])
        S5.append(vals[1])
        R.log(f"   (S) N={N}: N P_N at x = 0.3, 0.5: {vals[0]:.4f} {vals[1]:.4f}   formula {pred[0]:.4f} {pred[1]:.4f}"
              f"   (fresh L: {lw.lamperti(0.3, a):.4f} {lw.lamperti(0.5, a):.4f}), mass {PS.sum():.12f}")
        R.log(f"   [{time.time() - t0:.0f} s]")
    R.check("1. (R) ratio 0.815, 0.836, 0.855, increasing", [f"{r:.3f}" for r in ratios] == ["0.815", "0.836", "0.855"])
    prod = [(1 - r) * n ** 0.2 for r, n in zip(ratios, (500, 1000, 2000))]
    R.check("2. (R) (1 - ratio) N^0.2 within 5 percent across N, and the defect terms decrease",
            max(prod) / min(prod) < 1.05 and defects[0] > defects[1] > defects[2],
            ", ".join(f"{v:.4f}" for v in prod))
    R.check("3. (R) end layer ratios move toward 1",
            all(abs(endr[2][i] - 1) < abs(endr[0][i] - 1) for i in range(3)))
    R.check("4. (S) values 0.898, 1.325 (N = 500), 0.884, 1.299 (N = 2000), toward 0.8694, 1.2732 = 4/pi",
            [f"{S3[0]:.3f}", f"{S5[0]:.3f}", f"{S3[2]:.3f}", f"{S5[2]:.3f}"] == ["0.898", "1.325", "0.884", "1.299"]
            and abs(S3[2] - pred[0]) < abs(S3[0] - pred[0]) and abs(S5[2] - pred[1]) < abs(S5[0] - pred[1])
            and f"{pred[0]:.4f}" == "0.8694" and abs(pred[1] - 4 / np.pi) < 1e-8)
    R.check("5. total mass 1 to 10 digits", max(masses) < 1e-10, f"max defect {max(masses):.1e}")
    sys.exit(R.write(time.time() - t0))


if __name__ == "__main__":
    main()
