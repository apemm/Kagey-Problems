"""Certify the antimode j*_N of P_N on [pN, N] for the zeta law, alpha_+ = alpha_- = 1.5, fresh plus start.

For each N the exact law is computed by the run recursion of certify_atlas.py, with the a priori
relative error bound eps_N of that script. The antimode is certified when the value at every
other point of [pN, N] exceeds the minimum by more than the numerical error, that is when
    min_{k != k*} (P~(k) - P~(k*)) / P~(k*)  >  2 eps_N / (1 - eps_N),
so that the exact minimizer is the computed one. The script also records the two predictions of
Theorem thm:antimode, the law j = T_-^{-1}(2 alpha_+ s / N) (with the real extension
T(x) = zeta(alpha+1, x)/zeta(alpha+1) of the survival function) and the refined prediction
argmin_j [u_-(j) + C(j)/N] with C(j) of Theorem thm:second-order, on a grid of N for the figure.

Run from the paper folder:  py -I certify_antimode.py
Output: data/antimode.json. N = 8000 is included when its recursion takes under half an hour.
"""
import importlib.util
import json
import time
from datetime import date
from pathlib import Path

import numpy as np
from flint import arb, ctx

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("certify_atlas", HERE / "certify_atlas.py")
ca = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ca)

NS = [600, 1200, 2400, 4000, 8000]
TIME_LIMIT = 1800.0


def T_real(x):
    """Real extension of T(n) = P(X >= n): zeta(alpha+1, x)/zeta(alpha+1), as an arb ball."""
    a1 = arb(ca.ALPHA) + 1
    return a1.zeta(arb(x)) / a1.zeta()


def T_inverse(y):
    """The real x >= 1 with T_real(x) = y, by bisection (T_real is decreasing)."""
    old = ctx.prec
    ctx.prec = 128
    lo, hi = 1.0, 2.0
    while float(T_real(hi).mid()) > y:
        hi *= 2
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if float(T_real(mid).mid()) > y:
            lo = mid
        else:
            hi = mid
    ctx.prec = old
    return 0.5 * (lo + hi)


def main():
    mu = ca.means()
    s = 2 * mu
    alpha = ca.ALPHA
    J = 6000
    f, T = ca.law_arrays(max(NS) + 1)
    u, v = ca.renewal(f, J)
    C = ca.coefficient_C(u, v, mu)

    def refined(N):
        g = u + C / N
        return int(np.argmin(g[1:])) + 1

    rows = []
    t_start = time.time()
    for N in NS:
        if N == 8000 and rows:
            # predict the cost from the last run by the N^3 law
            last = rows[-1]
            est = last["runtime_s"] * (N / last["N"]) ** 3
            if est > TIME_LIMIT:
                print(f"skip N={N}: estimated {est:.0f}s")
                continue
        t0 = time.time()
        P = ca.occupation(N, f[:N + 2], T[:N + 2])
        rt = time.time() - t0
        eps = ca.apriori_bound(N)
        lo = N // 2                       # pN = N/2
        seg = P[lo:]
        i = int(np.argmin(seg))
        kstar = lo + i
        jstar = N - kstar
        others = np.delete(seg, i)
        gap_all = float((others.min() - seg[i]) / seg[i])
        gap_left = float((P[kstar - 1] - P[kstar]) / P[kstar])
        gap_right = float((P[kstar + 1] - P[kstar]) / P[kstar]) if kstar < N else None
        threshold = 2 * eps / (1 - eps)
        law = T_inverse(2 * alpha * s / N)
        row = {"N": N, "j_star": jstar, "k_star": kstar, "P_min": float(P[kstar]),
               "P_min_over_T_N": float(P[kstar] / T[N]),
               "rel_gap_to_j_star_minus_1": gap_right, "rel_gap_to_j_star_plus_1": gap_left,
               "min_rel_gap_over_[pN,N]": gap_all, "a_priori_eps": eps, "threshold_2eps": threshold,
               "certified": bool(gap_all > threshold),
               "mass_defect": float(abs(P.sum() - 1.0)),
               "law_T_inverse": law, "refined_argmin": refined(N), "runtime_s": rt,
               "P_near_min": {str(N - k): float(P[k]) for k in range(max(lo, kstar - 5), min(N, kstar + 5) + 1)}}
        rows.append(row)
        print(f"N={N}: j*={jstar} law={law:.2f} refined={refined(N)} gaps -/+ {gap_right:.2e}/{gap_left:.2e} "
              f"min gap {gap_all:.2e} vs 2eps {threshold:.1e} certified={row['certified']} ({rt:.1f}s)", flush=True)

    grid = np.unique(np.round(np.geomspace(400, 12000, 400)).astype(int))
    curves = {"N": [int(x) for x in grid],
              "law": [T_inverse(2 * alpha * s / x) for x in grid],
              "refined": [refined(x) for x in grid]}
    out = {
        "header": {"script": "certify_antimode.py", "script_sha256": ca.sha256_of(__file__),
                   "uses": {"certify_atlas.py": ca.sha256_of(HERE / "certify_atlas.py")},
                   "date": date.today().isoformat(),
                   "model": "zeta law for both signs, alpha=1.5, fresh plus start; antimode = argmin of P_N over [N/2, N], j* = N - argmin"},
        "mu": mu, "s": s, "alpha": alpha,
        "rows": rows, "curves": curves, "total_runtime_s": time.time() - t_start,
    }
    path = HERE / "data" / "antimode.json"
    path.write_text(json.dumps(out, indent=1))
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
