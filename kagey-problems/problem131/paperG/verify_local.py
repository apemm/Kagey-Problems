"""The numbers of Section sec:verify on the exact law: local law, end layers and sign changes.

Model: the zeta law f(n) = n^(-a-1)/zeta(a+1) for both signs (b = 1) and the fair start (a fresh
start of sign + or - with probability 1/2 each), so P_N(k) = (F+_N(k) + F+_N(N-k))/2.
  1. The ratio N P_N(k)/L(k/N) at k = N/2 for a = 0.5 is 1.0149, 1.0105, 1.0075 at
     N = 1000, 2000, 4000, and it decreases toward 1. Ratios at x = 0.05, ..., 0.5 for
     a = 0.3, 0.5, 0.7, 0.9 are printed.
  2. The number of sign changes of P_N(k+1) - P_N(k) is 1, 1, 3, 5 for a = 0.3, 0.5, 0.7, 0.9 at
     each N, with the changes at k = 104, 500, 896 (a = 0.7, N = 1000) and at k = 1, 142, 2000,
     3858, 3999 (a = 0.9, N = 4000).
  3. Near the threshold of thm:shape: 1 sign change for a = 0.58 and 3 for a = 0.61 at each N, at
     k = 344, 500, 656 for a = 0.61 and N = 1000.
  4. The end values: P_N(N)/T(N) = 1/2 exactly, P_N(N-1)/T(N) at a = 0.9 is 0.5754, 0.5737, 0.5727
     (tending to f(1) = 0.5715), and P_N(N-j)/(T(N) u(j)) for j = 1, ..., 5 at a = 0.5 lies within
     0.005 of 1 at N = 1000 and its largest deviation halves (within 10 percent) at N = 2000.
     The ten values are those of Table tab:ends.
  5. The uniform layer of thm:ends(b): P_N(N-j)/(T(N) u(j) Phi(j/N)) over 1 <= j <= 0.8N at a = 0.5
     lies in [1, 1.015] at N = 1000 and in [1, 1.011] at N = 2000.
  6. An asymmetric case, plus law zeta, minus law proportional to (n+3)^(-a-1), fresh plus start:
     the ratio N P_N(k)/L_{a,b}(k/N) at x = 0.1, ..., 0.9 moves toward 1 from N = 1000 to 4000 at
     a = 0.5, its range is [1.0121, 1.0397], [1.0069, 1.0199] at a = 0.5 and [0.8460, 1.2994],
     [0.8855, 1.1920] at a = 0.7 (N = 1000, 4000), and the number of sign changes is 2 at a = 0.5
     and 0.7 at each N.
  7. The total mass is 1 to 12 digits in every case (defect below 1e-12).
  8. Every entry of Table tab:ratios (the ratios at k = N/2 and k = N/20).

Run from the paper folder:  py -I verify_local.py     (about two minutes)
Output: data/verify_local_output.txt (with the sha256 of this script and the date).
Exit status 1 if any check fails.
"""
import importlib.util
import sys
import time
from pathlib import Path

import numpy as np
from scipy.special import zeta

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("lamperti_law", HERE / "lamperti_law.py")
lw = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lw)

R = lw.Report(__file__)
NS = (1000, 2000, 4000)
XS = (0.05, 0.1, 0.2, 0.3, 0.4, 0.5)


def fair_laws(a, nmax):
    f, T = lw.zeta_law(a, nmax)
    U = lw.convolution_powers(f, nmax)
    A, B = lw.arrays(U, U)
    u = U.sum(axis=0)
    out = {}
    for N in NS:
        if N > nmax:
            continue
        Pp = lw.fresh_plus(A, B, T, T, N)
        out[N] = 0.5 * (Pp + Pp[::-1])
    del A, B, U
    return f, T, u, out


def main():
    t0 = time.time()
    nmax = max(NS)
    R.log("verify_local.py: symmetric zeta law, fair start, N = 1000, 2000, 4000")
    masses = []
    counts = {}
    positions = {}
    centre = {}
    edge = {}
    for a in (0.3, 0.5, 0.7, 0.9, 0.58, 0.61):
        f, T, u, laws = fair_laws(a, nmax)
        R.log(f"\nalpha = {a}: f(1) = {f[1]:.4f}")
        R.log("   N P_N(k)/L(k/N) at x = " + " ".join(f"{x:5.2f}" for x in XS))
        for N, P in laws.items():
            masses.append(abs(P.sum() - 1))
            r = [N * P[round(x * N)] / lw.lamperti(round(x * N) / N, a) for x in XS]
            n, pos = lw.sign_changes(P)
            counts[(a, N)] = n
            positions[(a, N)] = pos
            centre[(a, N)] = r[-1]
            edge[(a, N)] = r[0]
            R.log(f"   N={N}: " + " ".join(f"{v:6.4f}" for v in r) + f"  | sign changes {n} at k = {pos}")
        if a == 0.9:
            endv = [laws[N][N - 1] / T[N] for N in NS]
            atom = [laws[N][N] / T[N] for N in NS]
            R.log("   P_N(N)/T(N): " + ", ".join(f"{v:.12f}" for v in atom))
            R.log("   P_N(N-1)/T(N): " + ", ".join(f"{v:.4f}" for v in endv) + f"   f(1) = {f[1]:.4f}")
            R.check("4a. P_N(N)/T(N) = 1/2 for the fair start", all(abs(v - 0.5) < 1e-12 for v in atom))
            R.check("4b. P_N(N-1)/T(N) at a = 0.9 is 0.5754, 0.5737, 0.5727, f(1) = 0.5715",
                    [f"{v:.4f}" for v in endv] == ["0.5754", "0.5737", "0.5727"] and f"{f[1]:.4f}" == "0.5715")
        if a == 0.5:
            dev = {}
            tab = {}
            for N in (1000, 2000):
                P = laws[N]
                rr = [P[N - j] / (T[N] * u[j]) for j in range(1, 6)]
                dev[N] = max(abs(v - 1) for v in rr)
                tab[N] = " ".join(f"{v:.4f}" for v in rr)
                R.log(f"   N={N}: P_N(N-j)/(T(N) u(j)), j = 1..5: " + " ".join(f"{v:.4f}" for v in rr))
            R.check("4c. end layer at a = 0.5 within 0.005 of 1 at N = 1000, deviation halves at N = 2000",
                    dev[1000] < 0.005 and 0.45 < dev[2000] / dev[1000] < 0.55,
                    f"max deviation {dev[1000]:.4f}, {dev[2000]:.4f}")
            R.check("4d. Table tab:ends", tab[1000] == "1.0009 1.0018 1.0026 1.0033 1.0040"
                    and tab[2000] == "1.0004 1.0009 1.0013 1.0017 1.0020")
            c = np.cos(np.pi * a)
            rng = {}
            for N in (1000, 2000):
                P = laws[N]
                js = np.arange(1, int(0.8 * N) + 1)
                y = js / N
                Phi = (1 - y) ** (a - 1) / ((1 - y) ** (2 * a) + 2 * c * (1 - y) ** a * y ** a + y ** (2 * a))
                rr = P[N - js] / (T[N] * u[js] * Phi)
                rng[N] = (rr.min(), rr.max())
                R.log(f"   N={N}: P_N(N-j)/(T(N) u(j) Phi(j/N)) over 1 <= j <= 0.8N in [{rr.min():.4f}, {rr.max():.4f}]")
            R.check("5. uniform layer in [1, 1.015] at N = 1000 and [1, 1.011] at N = 2000",
                    rng[1000][0] >= 1 and rng[1000][1] <= 1.015 and rng[2000][0] >= 1 and rng[2000][1] <= 1.011)
        R.log(f"   [{time.time() - t0:.0f} s]")

    got = [f"{centre[(0.5, N)]:.4f}" for N in NS]
    R.check("1. N P_N(N/2)/L(1/2) at a = 0.5 is 1.0149, 1.0105, 1.0075", got == ["1.0149", "1.0105", "1.0075"],
            ", ".join(got))
    R.check("2a. sign changes 1, 1, 3, 5 for a = 0.3, 0.5, 0.7, 0.9 at every N",
            all(counts[(a, N)] == n for a, n in ((0.3, 1), (0.5, 1), (0.7, 3), (0.9, 5)) for N in NS))
    R.check("2b. positions 104, 500, 896 (a = 0.7, N = 1000) and 1, 142, 2000, 3858, 3999 (a = 0.9, N = 4000)",
            positions[(0.7, 1000)] == [104, 500, 896] and positions[(0.9, 4000)] == [1, 142, 2000, 3858, 3999])
    R.check("3. sign changes 1 for a = 0.58 and 3 for a = 0.61 at every N, at 344, 500, 656 for a = 0.61, N = 1000",
            all(counts[(0.58, N)] == 1 and counts[(0.61, N)] == 3 for N in NS)
            and positions[(0.61, 1000)] == [344, 500, 656])

    table = {0.3: ("1.0852 1.0687 1.0555", "1.1023 1.0845 1.0694"),
             0.5: ("1.0149 1.0105 1.0075", "1.0045 1.0036 1.0028"),
             0.58: ("0.9846 0.9863 0.9883", "1.0142 1.0114 1.0090"),
             0.61: ("0.9696 0.9739 0.9781", "1.0282 1.0230 1.0185"),
             0.7: ("0.9023 0.9159 0.9285", "1.1202 1.1004 1.0833"),
             0.9: ("0.4903 0.5168 0.5433", "2.2892 2.1277 1.9905")}
    R.check("8. Table tab:ratios (ratios at k = N/2 and k = N/20)",
            all(" ".join(f"{centre[(a, N)]:.4f}" for N in NS) == c
                and " ".join(f"{edge[(a, N)]:.4f}" for N in NS) == e for a, (c, e) in table.items()))

    # 6. asymmetric case
    xs = (0.1, 0.3, 0.5, 0.7, 0.9)
    ok_counts = True
    toward = True
    ranges = {}
    for a in (0.5, 0.7):
        fp, Tp = lw.zeta_law(a, nmax)
        fm, Tm = lw.zeta_law(a, nmax, shift=3)
        b = zeta(a + 1) / zeta(a + 1, 4)
        Up = lw.convolution_powers(fp, nmax)
        Um = lw.convolution_powers(fm, nmax)
        A, B = lw.arrays(Up, Um)
        del Up, Um
        R.log(f"\nasymmetric a = {a}, b = {b:.4f}, fresh plus: N P_N(k)/L_b(k/N) at x = " + " ".join(f"{x:4.2f}" for x in xs))
        dist = []
        for N in NS:
            P = lw.fresh_plus(A, B, Tp, Tm, N)
            masses.append(abs(P.sum() - 1))
            r = [N * P[round(x * N)] / lw.lamperti(round(x * N) / N, a, b) for x in xs]
            ranges[(a, N)] = (f"{min(r):.4f}", f"{max(r):.4f}")
            n, pos = lw.sign_changes(P)
            ok_counts &= (n == 2)
            dist.append(max(abs(v - 1) for v in r))
            R.log(f"   N={N}: " + " ".join(f"{v:6.4f}" for v in r) + f"  | sign changes {n} at k = {pos}")
        if a == 0.5:
            toward = dist[0] > dist[1] > dist[2]
        del A, B
    R.check("6a. asymmetric case at a = 0.5: ratios move toward 1", toward)
    R.check("6c. asymmetric ranges [1.0121, 1.0397], [1.0069, 1.0199] (a = 0.5) and [0.8460, 1.2994], "
            "[0.8855, 1.1920] (a = 0.7) at N = 1000, 4000",
            ranges[(0.5, 1000)] == ("1.0121", "1.0397") and ranges[(0.5, 4000)] == ("1.0069", "1.0199")
            and ranges[(0.7, 1000)] == ("0.8460", "1.2994") and ranges[(0.7, 4000)] == ("0.8855", "1.1920"))
    R.check("6b. asymmetric case: 2 sign changes at a = 0.5 and 0.7 for every N", ok_counts)
    R.check("7. total mass 1 to 12 digits", max(masses) < 1e-12, f"max defect {max(masses):.1e}")
    sys.exit(R.write(time.time() - t0))


if __name__ == "__main__":
    main()
