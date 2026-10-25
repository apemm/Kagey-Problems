"""The numbers of Section sec:extrema (local extrema near the ends) quoted in Section sec:verify.

Model: the zeta law f(n) = n^(-5/2)/zeta(5/2) for both signs (alpha_+ = alpha_- = 3/2, p = 1/2).
The exact law comes from certify_atlas.occupation (the run recursion eq:run-recursion, fresh plus
start). A fresh minus start is the mirror image, since the two laws are equal, so the fair start is
(F(k) + F(N-k))/2. The start of Corollary cor:four-modes with d_0 = 5 is (F_N(k) + F_{N-5}(k))/2, by
Proposition prop:first-run.
  1. Lemma lem:diff-renewal: (u(j) - u(j-1)) mu^2 / T(j) at j = 10, 100, 1000.
     Printed: -0.963, -0.996, -0.9996.
  2. Theorem thm:first-diff, fresh plus start: the error N Delta R_N(j) - N Delta u(j) - Delta C(j) at
     j = 20 is 0.73 at N = 1000 and 0.23 at N = 3000, so it decays like 1/N (ratio between 2.5 and 3.5).
  3. The fair start (Conjecture conj:three-modes and the paragraph after it): exactly three modes, at
     k = 1, N/2, N-1, for N = 400 and 1000.
  4. Corollary cor:four-modes with d_0 = 5 at N = 1000: exactly four modes, at k = 1, 499, 995, 1000.
In 3 and 4 every relative difference |P(k+1) - P(k)|/max(P(k), P(k+1)) exceeds twice the a priori
relative error bound of certify_atlas.py, so the signs of all first differences, and hence the modes,
are certified.

Run from the paper folder:  py -I verify_modes.py
Output: data/verify_modes_output.txt (with the sha256 of this script and the date).
Exit status 1 if any check fails.
"""
import hashlib
import importlib.util
import platform
import sys
import time
from datetime import date
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, HERE / f"{name}.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


ca = load("certify_atlas")
LINES = []
FAILS = []


def log(msg=""):
    print(msg, flush=True)
    LINES.append(msg)


def check(name, cond, detail=""):
    log(f"{'PASS' if cond else 'FAIL'}  {name}" + (f"  ({detail})" if detail else ""))
    if not cond:
        FAILS.append(name)


def modes(P):
    """Strict local maxima, endpoints included when they beat their neighbour."""
    N = len(P) - 1
    out = []
    for k in range(N + 1):
        left = P[k - 1] if k > 0 else -np.inf
        right = P[k + 1] if k < N else -np.inf
        if P[k] > left and P[k] > right:
            out.append(k)
    return out


def min_rel_gap(P):
    return float(np.min(np.abs(np.diff(P)) / np.maximum(P[1:], P[:-1])))


def main():
    t0 = time.time()
    mu = ca.means()
    log("verify_modes.py: Section sec:extrema, zeta law, alpha = 3/2")
    f, T = ca.law_arrays(3005)
    u, v = ca.renewal(f, 3000)

    # 1. the difference renewal theorem
    ratios = [(u[j] - u[j - 1]) * mu ** 2 / T[j] for j in (10, 100, 1000)]
    log("   (u(j)-u(j-1)) mu^2/T(j) at j = 10, 100, 1000: " + ", ".join(f"{r:.6f}" for r in ratios))
    check("1. ratios -0.963, -0.996, -0.9996",
          [f"{ratios[0]:.3f}", f"{ratios[1]:.3f}", f"{ratios[2]:.4f}"] == ["-0.963", "-0.996", "-0.9996"])

    # 2. first differences in the layer, fresh plus start
    C = ca.coefficient_C(u[:60], v[:60], mu)
    j = 20
    err = {}
    for N in (1000, 3000):
        F = ca.occupation(N, f[:N + 2], T[:N + 2])
        R = F[N - np.arange(60)] / T[N]
        err[N] = N * (R[j + 1] - R[j]) - N * (u[j + 1] - u[j]) - (C[j + 1] - C[j])
        log(f"   N={N}: N dR - N du - dC at j = {j}: {err[N]:.4f}")
    q = err[1000] / err[3000]
    check("2. errors 0.73 (N = 1000) and 0.23 (N = 3000), ratio between 2.5 and 3.5",
          f"{err[1000]:.2f}" == "0.73" and f"{err[3000]:.2f}" == "0.23" and 2.5 < q < 3.5, f"ratio {q:.3f}")

    # 3. the fair start
    ok3 = True
    for N in (400, 1000):
        F = ca.occupation(N, f[:N + 2], T[:N + 2])
        P = 0.5 * (F + F[::-1])
        m, g, eps = modes(P), min_rel_gap(P), ca.apriori_bound(N)
        log(f"   fair start, N={N}: modes {m}, smallest relative gap {g:.2e}, a priori bound {eps:.2e}")
        ok3 = ok3 and m == [1, N // 2, N - 1] and g > 2 * eps
    check("3. fair start: modes at 1, N/2, N-1 for N = 400, 1000 (certified)", ok3)

    # 4. the prepared start of cor:four-modes, d_0 = 5
    N, d0 = 1000, 5
    F = ca.occupation(N, f[:N + 2], T[:N + 2])
    F5 = ca.occupation(N - d0, f[:N - d0 + 2], T[:N - d0 + 2])
    P = 0.5 * F
    P[:N - d0 + 1] += 0.5 * F5
    m, g, eps = modes(P), min_rel_gap(P), ca.apriori_bound(N)
    log(f"   prepared start, N={N}: modes {m}, smallest relative gap {g:.2e}, mass defect {abs(P.sum() - 1):.1e}")
    check("4. prepared start: four modes at 1, 499, 995, 1000 (certified)", m == [1, 499, 995, 1000] and g > 2 * eps)

    log(f"\n{'PASS' if not FAILS else 'FAIL'}  verify_modes ({len(FAILS)} failures, {time.time() - t0:.1f} s)")
    header = ["# script: verify_modes.py",
              f"# sha256: {hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}",
              f"# uses certify_atlas.py sha256: {ca.sha256_of(HERE / 'certify_atlas.py')}",
              f"# date: {date.today().isoformat()}",
              f"# python {platform.python_version()}, numpy {np.__version__}", ""]
    (HERE / "data" / "verify_modes_output.txt").write_text("\n".join(header + LINES) + "\n", encoding="utf-8")
    sys.exit(0 if not FAILS else 1)


if __name__ == "__main__":
    main()
