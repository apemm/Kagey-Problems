"""The numbers of Remark rem:no-single-formula (the double limit in Theorem thm:bigjump(b)).

Model: the zeta law f(n) = n^(-5/2)/zeta(5/2) for both signs (alpha_+ = alpha_- = 3/2, p = 1/2,
theta_+ = theta_- = 1), fresh plus start.
  1. The limit ratio h(K)/(alpha_+ (1-p)^alpha_+ K^(-alpha_+-1)) at K = 1, 4, 16, where h is the
     density of (Z_+ - Z_-)/2, by numerical inversion of exp(-c|t/2|^alpha), c = 2 K_alpha |cos(pi alpha/2)|.
     Printed: 0.31, 1.68, 1.09.
  2. The exact ratio P_N(k)/G_N(k) at k = ceil(pN + K B_N), with B_N = a(N/s) and a the inverse of the
     real extension T(x) = zeta(alpha+1, x)/zeta(alpha+1) (so that (N/s) T(B_N) = 1), and G_N the kernel
     of eq:G with the exact coefficient gamma of eq:gamma. Printed: 0.354, 1.482, 1.036 at N = 1200 and
     0.337, 1.538, 1.059 at N = 3000.
  3. The exact ratios move toward the limits of item 1 from N = 1200 to N = 3000, and at N = 3000 the
     relative distance to the limit at K = 1 and K = 4 is 7 or 8 percent after rounding.

Run from the paper folder:  py -I verify_bigjump.py
Output: data/verify_bigjump_output.txt (with the sha256 of this script and the date).
Exit status 1 if any check fails.
"""
import hashlib
import importlib.util
import math
import platform
import sys
import time
from datetime import date
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.special import gamma

HERE = Path(__file__).resolve().parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, HERE / f"{name}.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


ca = load("certify_atlas")
cm = load("certify_antimode")
LINES = []
FAILS = []


def log(msg=""):
    print(msg, flush=True)
    LINES.append(msg)


def check(name, cond, detail=""):
    log(f"{'PASS' if cond else 'FAIL'}  {name}" + (f"  ({detail})" if detail else ""))
    if not cond:
        FAILS.append(name)


def main():
    t0 = time.time()
    a = ca.ALPHA
    mu = ca.means()
    s = 2 * mu
    p = 0.5
    Ks = (1, 4, 16)
    log("verify_bigjump.py: Remark rem:no-single-formula, zeta law, alpha = 3/2, fresh plus start")

    # 1. the limit ratio
    Ka = -gamma(1 - a)
    c = 2 * Ka * abs(math.cos(math.pi * a / 2))

    def h(x):
        val, _ = quad(lambda t: np.exp(-c * (t / 2) ** a), 0, np.inf, weight="cos", wvar=x, limit=400)
        return val / math.pi
    lim = {K: h(K) / (a * (1 - p) ** a * K ** (-a - 1)) for K in Ks}
    log("   h(K)/(alpha (1-p)^alpha K^(-alpha-1)): " + ", ".join(f"K={K}: {lim[K]:.4f}" for K in Ks))
    check("1. limit ratios 0.31, 1.68, 1.09 at K = 1, 4, 16", [f"{lim[K]:.2f}" for K in Ks] == ["0.31", "1.68", "1.09"])

    # 2. exact ratios
    printed = {1200: ["0.354", "1.482", "1.036"], 3000: ["0.337", "1.538", "1.059"]}
    got = {}
    for N in (1200, 3000):
        t1 = time.time()
        f, T = ca.law_arrays(N + 2)
        P = ca.occupation(N, f, T)
        u, _ = ca.renewal(f, N)
        gam = np.zeros(N + 1)
        for j in range(1, N + 1):
            gam[j] = np.dot(u[:j], 1.0 + mu * u[j:0:-1])     # kappa^(+)_+ = u_-
        BN = cm.T_inverse(s / N)
        row = []
        for K in Ks:
            k = math.ceil(p * N + K * BN)
            L = (k - p * N) / (1 - p)
            Lf = int(math.floor(L))
            j = N - k
            G = gam[j] * f[Lf] + T[Lf] * u[j]
            row.append(P[k] / G)
            log(f"   N={N}, K={K}: B_N = {BN:.3f}, k = {k}, P_N(k)/G_N(k) = {P[k] / G:.4f}")
        got[N] = row
        log(f"   N={N}: {time.time() - t1:.1f} s, mass defect {abs(P.sum() - 1):.1e}")
    check("2. exact ratios 0.354, 1.482, 1.036 (N = 1200) and 0.337, 1.538, 1.059 (N = 3000)",
          all([f"{x:.3f}" for x in got[N]] == printed[N] for N in printed))

    # 3. toward the limits
    toward = all(abs(got[3000][i] - lim[K]) < abs(got[1200][i] - lim[K]) for i, K in enumerate(Ks))
    off = [abs(got[3000][i] / lim[K] - 1) for i, K in enumerate(Ks[:2])]
    check("3. the ratios move toward the limits, and at N = 3000 they are 7 to 8 percent off at K = 1, 4 (rounded)",
          toward and all(round(100 * o) in (7, 8) for o in off), ", ".join(f"{100 * o:.1f}%" for o in off))

    log(f"\n{'PASS' if not FAILS else 'FAIL'}  verify_bigjump ({len(FAILS)} failures, {time.time() - t0:.1f} s)")
    header = [f"# script: verify_bigjump.py",
              f"# sha256: {hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}",
              f"# uses certify_atlas.py sha256: {ca.sha256_of(HERE / 'certify_atlas.py')}",
              f"# uses certify_antimode.py sha256: {ca.sha256_of(HERE / 'certify_antimode.py')}",
              f"# date: {date.today().isoformat()}",
              f"# python {platform.python_version()}, numpy {np.__version__}", ""]
    (HERE / "data" / "verify_bigjump_output.txt").write_text("\n".join(header + LINES) + "\n", encoding="utf-8")
    sys.exit(0 if not FAILS else 1)


if __name__ == "__main__":
    main()
