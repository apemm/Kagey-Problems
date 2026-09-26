"""Guards and spot checks for the crossing at every N (Paper A, Theorem thm:every-n), added
after a second check of the proofs.
Standard library only.  Runtime under a minute (predicted < 2 min).

  G1  rounding guard of verify_every_n_sign.py: v - u_zeta > 1e-40 for N = 1001..2773.
  G2  rounding guard of section [6] of verify_every_n.py at N = 15, 16, 218, 219.
  G3  sign of z_N - zeta_N from the certificate integers in data/every_n_certificates.csv, N <= 1000.
  G4  sign of R_N from the same integers (ledger prediction P7, not used in the paper).
  G5  z_2 = 2/3 < log 2 (Proposition prop:crossing-eq at N = 2).
  G6  run-count integer vs integer DP at a few N in the single-method range 401..2773, with timings.
  G7  Corollary cor:every-n(d): f(zeta_N) - 1 at N = 2773 and 2774, robust to the 1e-45 bracket.

Output: data/every_n_guards_output.txt
"""
import csv
import time
from decimal import Decimal as D, getcontext
from fractions import Fraction

import verify_every_n as v

getcontext().prec = 60
TINY = D(10) ** -40
OUT = []


def out(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    OUT.append(s)


def main():
    t0 = time.time()
    out("verify_every_n_guards.py  run " + time.strftime("%Y-%m-%d %H:%M"))

    # G1
    DEN = 10 ** 7
    gmin = None
    eq = []
    for N in range(1001, 2774):
        zt = v.zeta_dec(N)
        uz = zt / (N - zt)
        a = int((uz * DEN).to_integral_value(rounding="ROUND_CEILING"))
        gap = D(a) / DEN - uz
        if gap == 0:
            eq.append(N)
        if gmin is None or gap < gmin[1]:
            gmin = (N, gap)
    out(f"[G1] N = 1001..2773: v = u_zeta exactly at {eq}; smallest v - u_zeta = {float(gmin[1]):.3e} at N = {gmin[0]};"
        f" all > 1e-40: {gmin[1] > TINY}")

    # G2
    den2 = 10 ** 30
    worst = None
    for N in (15, 16, 218, 219):
        zt = v.zeta_dec(N)
        uz = zt / (N - zt)
        aa = int((uz * den2).to_integral_value(rounding="ROUND_FLOOR"))
        g1 = uz - D(aa) / den2
        g2 = D(aa + 1) / den2 - uz
        for g in (g1, g2):
            if worst is None or g < worst[1]:
                worst = (N, g)
    out(f"[G2] section [6] guard at N = 15, 16, 218, 219: smallest distance to the 1e-30 grid = {float(worst[1]):.3e}"
        f" at N = {worst[0]}; all > 1e-40: {worst[1] > TINY}")

    # G3, G4 from the certificate integers
    rows = []
    with open("data/every_n_certificates.csv") as f:
        for r in csv.DictReader(f):
            rows.append((int(r["N"]), int(r["u_lo_times_1e9"]), int(r["u_hi_times_1e9"])))
    b = 10 ** 9
    C0 = v.C0
    sign = {}
    dmin = None
    rhi_max = None
    rlo_small = {}
    for (N, a, a1) in rows:
        zlo = D(N * a) / D(a + b)          # z(a/b) = N a/(a+b)
        zhi = D(N * a1) / D(a1 + b)
        zt = v.zeta_dec(N)
        if zlo > zt:
            sign[N], dist = 1, zlo - zt
        elif zhi < zt:
            sign[N], dist = -1, zt - zhi
        else:
            sign[N], dist = 0, D(0)
        if dmin is None or dist < dmin[1]:
            dmin = (N, dist)
        K = D(N).ln() + C0
        Rhi = v.psi(zhi) - K - 1 / (8 * zhi)
        Rlo = v.psi(zlo) - K - 1 / (8 * zlo)
        if N >= 4 and (rhi_max is None or Rhi > rhi_max[1]):
            rhi_max = (N, Rhi)
        if N <= 3:
            rlo_small[N] = Rlo
    und = [N for N in sign if sign[N] == 0]
    pat = ([N for N in sign if N <= 15 and sign[N] != 1] + [N for N in sign if 16 <= N <= 218 and sign[N] != -1]
           + [N for N in sign if N >= 219 and sign[N] != 1])
    out(f"[G3] N = 2..{max(sign)}: undecided at {und}; deviations from (+ for N<=15, - for 16..218, + for 219..1000): {pat}")
    out(f"     smallest distance from zeta_N to [z(a/b), z(a'/b)] = {float(dmin[1]):.4e} at N = {dmin[0]}")
    out(f"[G4] max over 4 <= N <= 1000 of R(z(a'/b)) = {float(rhi_max[1]):+.6f} at N = {rhi_max[0]};"
        f" R(z(a/b)) at N = 2, 3: {float(rlo_small[2]):+.6f}, {float(rlo_small[3]):+.6f}")

    # G5
    z2 = Fraction(2) * Fraction(1, 2) / (1 + Fraction(1, 2))
    gap = D(2).ln() - D(z2.numerator) / D(z2.denominator)
    e2 = D(2).exp()
    out(f"[G5] z_2 = {z2}; log 2 - z_2 = {gap:.8f}; e^2 = {e2:.6f} < 8: {e2 < 8}")

    # G6
    for N in (401, 1000, 1008, 2000, 2773):
        zt = v.zeta_dec(N)
        uz = zt / (N - zt)
        a = int((uz * DEN).to_integral_value(rounding="ROUND_CEILING"))
        target = DEN ** (N - 1)
        t1 = time.time()
        rc = v.S_int_runcount2(v.runcount_coeffs(N), a, DEN)
        trc = time.time() - t1
        t1 = time.time()
        dp = v.S_int_dp(N, a, DEN)
        tdp = time.time() - t1
        out(f"[G6] N = {N}: run-count == DP: {rc == dp}; S_N(v) < 1: {rc < target};"
            f" 1 - S_N(v) = {float(1 - D(rc) / D(target)):.4e}; time run-count {trc:.2f}s, DP {tdp:.2f}s")

    # G7: z_N > zeta_N once g(zeta_N) > 1, where g(z) = N (1/(8z) - 1/(16z^2)) / (z(z+1)) at the
    # given N equals f(zeta_N) of the proof. g decreases in z, and zeta_dec is within 1e-45 of zeta_N.
    h = D(10) ** -45
    for N in (2773, 2774):
        zt = v.zeta_dec(N)
        g = lambda z: D(N) * (1 / (8 * z) - 1 / (16 * z * z)) / (z * (z + 1))
        val = g(zt) - 1
        safe = (g(zt + h) > 1) if N == 2774 else (g(zt - h) < 1)
        out(f"[G7] N = {N}: f(zeta_N) - 1 = {float(val):+.5e}; "
            f"{'f > 1 at zeta_N + 1e-45' if N == 2774 else 'f < 1 at zeta_N - 1e-45'}: {safe}")
    out(f"total time {time.time()-t0:.1f}s")
    with open("data/every_n_guards_output.txt", "w") as f:
        f.write("\n".join(OUT) + "\n")


if __name__ == "__main__":
    main()
