"""Exact sign of z_N - zeta_N for 1001 <= N <= 2773 (Paper A, Remark rem:sign).  Standard library only.

verify_every_n.py settles the sign exactly for N <= 1000 (certificates) and the crossing theorem
gives z_N > zeta_N for N >= 2774.  Here, for every N in between, take the rational
v = ceil(10^7 u_zeta)/10^7 >= u_zeta = zeta_N/(N - zeta_N) and check S_N(v) < 1 in exact integers
(run-count coefficients).  Then u_N > v >= u_zeta, i.e. z_N > zeta_N.  The float DP of
verify_every_n.py (section [6]) is the second, independent method on this range.
Runtime about 13 minutes (775 s on 2026-09-26).

Output: data/every_n_sign_output.txt
"""
import time
from decimal import Decimal as D

import verify_every_n as v

LO, HI, DEN = 1001, 2773, 10 ** 7


def main():
    t0 = time.time()
    bad = []
    min_gap = None
    for N in range(LO, HI + 1):
        zt = v.zeta_dec(N)
        uz = zt / (N - zt)
        a = int((uz * DEN).to_integral_value(rounding="ROUND_CEILING"))
        # v > u_zeta with room for the 1e-45 error in zeta_N (min gap 1.2e-11: verify_every_n_guards.py [G1])
        assert D(a) / DEN - uz > D(10) ** -40, N
        W = v.runcount_coeffs(N)
        target = DEN ** (N - 1)
        val = v.S_int_runcount2(W, a, DEN)
        if not val < target:
            bad.append(N)
        gap = 1 - D(val) / D(target)
        if min_gap is None or gap < min_gap[1]:
            min_gap = (N, gap)
    lines = [
        "verify_every_n_sign.py  run " + time.strftime("%Y-%m-%d %H:%M"),
        f"N = {LO}..{HI}: S_N(v) < 1 exactly (so z_N > zeta_N) fails at {bad}",
        f"smallest 1 - S_N(v) = {float(min_gap[1]):.3e} at N = {min_gap[0]}",
        f"time {time.time()-t0:.1f}s",
    ]
    print("\n".join(lines))
    with open("data/every_n_sign_output.txt", "w") as f:
        f.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
