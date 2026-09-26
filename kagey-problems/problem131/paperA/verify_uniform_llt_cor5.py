"""Run 4 of the uniform local law checks (Problem 131, Paper A): where the central crossing bound
of Remark rem:llt-center stops being vacuous,
and the closed form for bins 1 and N-1.

Standard library only (fractions, decimal, math).  Reuses the run-3 routines of
verify_uniform_llt.py (exact_uN, centre_S_coeffs, dp_row).

That bound needs eta = 221 q_N + 5825 q_N^2 < 1, i.e. q_N < q* (positive root of
5825 q^2 + 221 q - 1).  For even N, eta < 1 <=> S_N(u*) > 1 <=> P_N(N/2) > P_N(0) at q = q*.

  P15  q* in Decimal and in float.
  P16  sign of eta - 1 for every even 4 <= N <= 2000, two ways:
         method 1: sign of S_N(u*) - 1, integer coefficients, 50-digit Decimal Horner;
         method 2: sign of P_N(N/2) - P_N(0) at q = q*, one float run of the recursion eq:dp.
  P17  q_N and eta at selected N: Decimal bisection (exact_uN), certified by a sign change of
       P_N(N/2) - P_N(0) from the float recursion at q_N (1 -+ 1e-7).
  P18  P_N(1) = P_N(N-1) = q p^{N-2} + (N-2) q^2 p^{N-3} / 2 against the recursion in Fractions.

Output: data/uniform-llt-verification-run4.txt
"""
from fractions import Fraction
from decimal import Decimal, getcontext
import math
import os
import time

from verify_uniform_llt import exact_uN, centre_S_coeffs, dp_row

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")


def qstar_decimal():
    getcontext().prec = 50
    return (Decimal(-221) + Decimal(221 * 221 + 4 * 5825).sqrt()) / Decimal(2 * 5825)


def qstar_float():
    # bisection on 5825 q^2 + 221 q - 1 (independent of the closed form)
    lo, hi = 0.0, 0.01
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if 5825 * mid * mid + 221 * mid - 1 > 0:
            hi = mid
        else:
            lo = mid
    return 0.5 * (lo + hi)


def sign_method1(N, ustar):
    getcontext().prec = 50
    val = Decimal(0)
    for w in reversed(centre_S_coeffs(N)):
        val = val * ustar + Decimal(w)
    return 1 if val > 1 else -1          # +1 <=> S_N(u*) > 1 <=> eta < 1


def signs_method2(Nmax, q):
    """One run of eq:dp in float; returns {N: sign(P_N(N/2) - P_N(0))} for even N."""
    p = 1.0 - q
    R = [0.0, 0.5]
    L = [0.5, 0.0]
    out = {}
    for n in range(2, Nmax + 1):
        R2 = [0.0] * (n + 1)
        L2 = [0.0] * (n + 1)
        for k in range(1, n + 1):
            R2[k] = p * R[k - 1] + q * L[k - 1]
        for k in range(0, n):
            L2[k] = p * L[k] + q * R[k]
        R, L = R2, L2
        if n % 2 == 0 and n >= 4:
            mid = R[n // 2] + L[n // 2]
            end = R[0] + L[0]
            out[n] = 1 if mid > end else -1
    return out


def dp_sign(N, q):
    row = dp_row(N, q)
    return 1 if row[N // 2] > row[0] else -1


def main():
    t0 = time.time()
    lines = []
    qs_d = qstar_decimal()
    qs_f = qstar_float()
    lines.append(f"P15 q* = {qs_d:.12f} (closed form, Decimal) ; {qs_f:.12f} (bisection, float)")
    getcontext().prec = 50
    ustar = qs_d / (1 - qs_d)

    Ns = list(range(4, 2001, 2))
    s1 = {N: sign_method1(N, ustar) for N in Ns}
    t1 = time.time()
    s2 = signs_method2(2000, float(qs_d))
    t2 = time.time()
    disagree = [N for N in Ns if s1[N] != s2[N]]
    first_pos = min(N for N in Ns if s1[N] > 0)
    monotone = all(s1[N] < 0 for N in Ns if N < first_pos) and all(s1[N] > 0 for N in Ns if N >= first_pos)
    lines.append(f"P16 even 4<=N<=2000: N* (smallest even N with eta<1) = {first_pos}; "
                 f"sign pattern monotone = {monotone}; method1/method2 disagreements = {len(disagree)} {disagree[:10]}"
                 f" (method 1 {t1 - t0:.1f} s, method 2 {t2 - t1:.1f} s)")

    for N in [1000, 1400, first_pos - 2, first_pos, 1500, 1600]:
        uN = exact_uN(N)
        qN = float(uN / (1 + uN))
        eta = 221 * qN + 5825 * qN * qN
        lo = dp_sign(N, qN * (1 - 1e-7))
        hi = dp_sign(N, qN * (1 + 1e-7))
        cert = (lo < 0 and hi > 0)
        if eta < 1:
            rel = eta / ((1 - eta) * (N - 1) * qN)
            rtxt = f"relative bound eta/((1-eta)(N-1)q_N) = {rel:.4f}"
        else:
            rtxt = "relative bound: none (eta >= 1)"
        lines.append(f"P17 N={N}: q_N = {qN:.10e}; eta = {eta:.5f}; recursion sign change across q_N(1-+1e-7): "
                     f"{cert}; {rtxt}")

    mism = 0
    cnt = 0
    for q in [Fraction(1, 2), Fraction(1, 3), Fraction(1, 7), Fraction(2, 11), Fraction(9, 10)]:
        p = 1 - q
        for N in range(2, 41):
            row = dp_row(N, q)
            closed = q * p ** (N - 2) + Fraction(N - 2, 2) * q * q * p ** (N - 3) if N >= 3 else q
            for k in (1, N - 1):
                cnt += 1
                if row[k] != closed:
                    mism += 1
    lines.append(f"P18 P_N(1)=P_N(N-1) closed form vs recursion in Fractions: {cnt} cases, mismatches = {mism}")
    lines.append(f"elapsed {time.time() - t0:.1f} s")
    with open(os.path.join(DATA, "uniform-llt-verification-run4.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
