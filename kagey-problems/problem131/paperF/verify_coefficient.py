"""The coefficient C(j) of Theorem thm:second-order and the antimode of Theorem thm:antimode.

Model: the zeta law f(n) = n^(-5/2)/zeta(5/2) for both signs (alpha_+ = alpha_- = 3/2), fresh plus
start. The exact law P_N is computed by the run recursion of certify_atlas.py (double precision,
a priori relative error eps_N <= 1.1e-8 for N <= 4800). The renewal quantities u_-, v_- are
sums of nonnegative terms in double precision.

Checks (labels of problem131_levy.tex):
  1. eq:Cj        the two forms of C(j) agree for j <= 6000;
  2. eq:Cj        C(j)/j at j = 5, ..., 320 and the limit 2 alpha_+ s/mu_-^2 = 3.0811 as printed
                  after the proof of Theorem thm:second-order, and C(j)/j decreases to the limit;
  3. thm:second-order  the finite-N excess [P_N(N-j)/T_+(N) - u_-(j)] N/j at N = 1200, 2400, 4800
                  for j = 5, 10, 20, 40 (the table of Section 8.2 of the plan review of
                  October 23, 2026), and its distance to C(j)/j decreases as N doubles;
  4. prop:final-run  the explicit final-run identity (eq:final-explicit) against the recursion, N = 1200, j <= 40;
  5. thm:antimode, Table tab:antimode  the refined prediction argmin_j [u_-(j) + C(j)/N], the
                  leading prediction (smallest j with T_-(j) < 2 alpha_+ s/N) and the ratio
                  N T_-(j*_N)/(2 alpha_+ s), against the certified antimodes of data/antimode.json,
                  and the certificates themselves (separation margin above 2 eps_N);
  6. eq:second-renewal  the ratio of the two sides at j = 40, 160, 640 (within 0.001 of the printed values);
  7. thm:mode(d)  the constant C(phi) = 0.7761317205..., 1/C(phi) = 1.2884... and the bound 0.9513...;
  8. the certificate data/atlas_N5000.json of certify_atlas.py: the a priori bound, the mass defect,
                  the ball-arithmetic comparison at N = 600 and the script hash.

Run from the paper folder:  py -I verify_coefficient.py
Output: data/verify_coefficient_output.txt (with the sha256 of this script and the date).
Exit status 1 if any check fails.
"""
import hashlib
import importlib.util
import json
import platform
import sys
import time
from datetime import date
from pathlib import Path

import numpy as np
import mpmath as mp

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("certify_atlas", HERE / "certify_atlas.py")
ca = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ca)

LINES = []
FAILS = []


def log(msg=""):
    print(msg, flush=True)
    LINES.append(msg)


def check(name, cond, detail=""):
    log(f"{'PASS' if cond else 'FAIL'}  {name}" + (f"  ({detail})" if detail else ""))
    if not cond:
        FAILS.append(name)


def r3(x):
    return float(f"{x:.3f}")


def main():
    t0 = time.time()
    alpha = ca.ALPHA
    mu = ca.means()
    s = 2 * mu
    J = 6000
    f, T = ca.law_arrays(max(J, 8000) + 2)
    u, v = ca.renewal(f, J)
    C = ca.coefficient_C(u, v, mu)                       # second form of eq:Cj
    jj = np.arange(J + 1)
    cu = np.concatenate([[0.0], np.cumsum(u[:-1])])      # sum_{i<j} u(i)
    C1 = alpha * (jj * u + 2 * mu * v + cu)              # first form of eq:Cj
    limit = 2 * alpha * s / mu ** 2
    log("verify_coefficient.py: zeta law, alpha_+ = alpha_- = 3/2, fresh plus start")
    log(f"mu = {mu:.12f}, s = {s:.12f}, 2 alpha s/mu^2 = {limit:.6f}")

    # 1. two forms
    rel = float(np.max(np.abs(C1[1:] - C[1:]) / C[1:]))
    check("1. eq:Cj, the two forms agree for 1 <= j <= 6000", rel < 1e-12, f"max rel diff {rel:.2e}")

    # 2. C(j)/j as printed
    js = [5, 10, 20, 40, 80, 160, 320]
    printed = [4.968, 4.430, 4.041, 3.762, 3.563, 3.422, 3.323]
    got = [C[j] / j for j in js]
    log("   C(j)/j: " + "  ".join(f"j={j}: {g:.4f}" for j, g in zip(js, got)))
    check("2a. C(j)/j at j = 5,...,320 as printed (3 decimals)", [r3(g) for g in got] == printed)
    check("2b. limit 2 alpha_+ s/mu_-^2 = 3.0811 as printed", f"{limit:.4f}" == "3.0811", f"{limit:.6f}")
    ratio = C[1:] / jj[1:]
    check("2c. C(j)/j decreases and stays above the limit, 1 <= j <= 6000",
          bool(np.all(np.diff(ratio) < 0) and np.all(ratio > limit)),
          f"C(6000)/6000 = {ratio[-1]:.4f}")

    # 3. finite-N excess, Section 8.2 of the plan review
    table = {1200: [5.058, 4.596, 4.347, 4.354], 2400: [5.013, 4.512, 4.189, 4.040],
             4800: [4.990, 4.471, 4.114, 3.897]}
    jt = [5, 10, 20, 40]
    plan_limit = [4.968, 4.430, 4.041, 3.762]
    log("   j | C(j)/j | excess N/j at N = 1200, 2400, 4800")
    exc = {}
    runtimes = {}
    Ps = {}
    for N in (1200, 2400, 4800):
        t1 = time.time()
        P = ca.occupation(N, f[:N + 2], T[:N + 2])
        runtimes[N] = time.time() - t1
        Ps[N] = P
        exc[N] = [(P[N - j] / T[N] - u[j]) * N / j for j in jt]
        log(f"   N={N}: recursion {runtimes[N]:.1f} s, mass defect {abs(P.sum() - 1):.1e}, "
            f"a priori bound {ca.apriori_bound(N):.1e}")
    for i, j in enumerate(jt):
        log(f"   {j:3d} | {C[j] / j:.3f} | " + "  ".join(f"{exc[N][i]:.3f}" for N in (1200, 2400, 4800)))
    check("3a. C(j)/j column as in the plan review", [r3(C[j] / j) for j in jt] == plan_limit)
    check("3b. finite-N excess as in the plan review (3 decimals)",
          all([r3(x) for x in exc[N]] == table[N] for N in table))
    dist = {N: [abs(exc[N][i] - C[j] / j) for i, j in enumerate(jt)] for N in exc}
    check("3c. |excess - C(j)/j| decreases from N = 1200 to 2400 to 4800 for each j",
          all(dist[1200][i] > dist[2400][i] > dist[4800][i] for i in range(len(jt))),
          "distances " + "; ".join(",".join(f"{d:.3f}" for d in dist[N]) for N in (1200, 2400, 4800)))

    # 4. explicit final-run identity at N = 1200, j <= 40
    N, Jx = 1200, 40
    fa = np.concatenate([[0.0], f[1:N + 1]])
    U = [np.zeros(N + 1) for _ in range(Jx + 2)]
    U[0][0] = 1.0
    for r in range(1, Jx + 2):
        U[r] = np.convolve(U[r - 1], fa)[:N + 1]
    P = Ps[1200]
    err = 0.0
    for j in range(Jx + 1):
        s1 = sum(U[r][j] * np.dot(U[r][:N - j], T[N - j - np.arange(N - j)]) for r in range(0, j + 1))
        s2 = sum(T[m] * U[r][j - m] * U[r + 1][N - j] for m in range(1, j + 1) for r in range(0, j - m + 1))
        err = max(err, abs(s1 + s2 - P[N - j]) / P[N - j])
    check("4. prop:final-run (eq:final-explicit) against the recursion, N = 1200, j <= 40", err < 1e-10, f"max rel diff {err:.1e}")

    # 5. the antimode table
    am = json.loads((HERE / "data" / "antimode.json").read_text())
    tab = {600: (7, 7, 10, 1.534), 1200: (11, 12, 15, 1.498), 2400: (19, 20, 23, 1.282),
           4000: (27, 28, 32, 1.247), 8000: (44, 45, 50, 1.186)}
    log(f"   antimode.json: script sha256 {am['header']['script_sha256'][:16]}..., date {am['header']['date']}")
    log("   N | j* | refined | leading | N T(j*)/(2 alpha s) | min rel gap | 2 eps_N | certified")
    ok_tab, ok_cert, ok_ref = True, True, True
    for row in am["rows"]:
        N = row["N"]
        g = u[:N // 2 + 1] + C[:N // 2 + 1] / N
        ref = int(np.argmin(g[1:])) + 1
        lead = int(np.argmax(T[1:] < 2 * alpha * s / N)) + 1
        js_ = row["j_star"]
        rat = N * T[js_] / (2 * alpha * s)
        gap = row["min_rel_gap_over_[pN,N]"]
        thr = row["threshold_2eps"]
        cert = bool(row["certified"]) and gap > thr
        log(f"   {N} | {js_} | {ref} | {lead} | {rat:.3f} | {gap:.2e} | {thr:.1e} | {cert}")
        ok_cert &= cert
        ok_ref &= (ref == row["refined_argmin"]) and abs(ref - js_) <= 1
        ok_tab &= (N in tab) and tab[N] == (js_, ref, lead, r3(rat))
    check("5a. certified antimodes: the value at every other point of [pN, N] exceeds the minimum by more than 2 eps_N", ok_cert)
    check("5b. refined prediction argmin_j [u_-(j) + C(j)/N] is within 1 of j*_N and agrees with antimode.json", ok_ref)
    check("5c. Table tab:antimode reproduced (all five rows, all columns)",
          ok_tab and sorted(r["N"] for r in am["rows"]) == sorted(tab))

    # 6. second-order renewal theorem
    jr = [40, 160, 640]
    rr = [(u[j] - 1 / mu) / (j * T[j] / (mu ** 2 * (alpha - 1))) for j in jr]
    log("   (u(j) - 1/mu)/(j T(j)/(mu^2 (alpha-1))): " + "  ".join(f"j={j}: {x:.4f}" for j, x in zip(jr, rr)))
    check("6. eq:second-renewal ratio 0.978, 0.995, 0.999 at j = 40, 160, 640, each within 0.001",
          all(abs(x - y) <= 1e-3 for x, y in zip(rr, [0.978, 0.995, 0.999])))

    # 7. the constant of Theorem thm:mode(d)
    mp.mp.dps = 30
    phi = (1 + mp.sqrt(5)) / 2

    def Ccal(a):
        K = -mp.gamma(1 - a)
        return mp.pi * (K * abs(mp.cos(mp.pi * a / 2))) ** (1 / a) / (4 * (a - 1) * mp.gamma(1 + 1 / a) * mp.zeta(a) ** (1 + 1 / a))
    c_phi = Ccal(phi)
    c_alt = mp.pi * phi * (phi * mp.gamma(phi ** -2) * abs(mp.cos(mp.pi * phi / 2))) ** (1 / phi) / (4 * mp.gamma(phi) * mp.zeta(phi) ** phi)
    bound = mp.pi * phi * (mp.sqrt(3) * phi ** 3 / 2) ** (1 / phi) / (4 * mp.mpf("0.8856") * (phi + mp.mpf(1) / 2) ** phi)
    log(f"   C(phi) = {mp.nstr(c_phi, 15)}, closed form {mp.nstr(c_alt, 15)}, 1/C(phi) = {mp.nstr(1 / c_phi, 8)}, "
        f"bound {mp.nstr(bound, 8)}")
    check("7. thm:mode(d): C(phi) = 0.7761317205..., 1/C(phi) = 1.2884..., elementary bound 0.9513 (rounded) < 1",
          mp.floor(c_phi * 10 ** 10) == 7761317205 and abs(c_phi - c_alt) < mp.mpf(10) ** -25
          and mp.floor(10 ** 4 / c_phi) == 12884 and abs(bound - mp.mpf("0.9513")) < mp.mpf("1e-4") and bound < 1
          and mp.gamma(mp.findroot(lambda x: mp.diff(mp.gamma, x), 1.46)) > mp.mpf("0.8856"))

    # 8. the certificate of the exact law behind Figure 1(a)
    at = json.loads((HERE / "data" / "atlas_N5000.json").read_text())
    bc = at["ball_check"]
    log(f"   atlas_N5000.json: N = {at['N']}, mass defect {at['mass_defect']:.1e}, a priori bound "
        f"{at['a_priori_relative_bound']:.2e}; ball check N = {bc['N']}: max rel dev {bc['max_rel_dev_double_vs_ball']:.1e}, "
        f"max rel radius {bc['max_rel_ball_radius']:.1e}")
    check("8. data/atlas_N5000.json: a priori bound eps_5000 < 3e-9, mass defect below it, "
          "double precision inside the 128-bit balls (plus eps_600) at N = 600",
          at["a_priori_relative_bound"] < 3e-9 and at["mass_defect"] < at["a_priori_relative_bound"]
          and bc["double_within_ball_plus_apriori"] and bc["max_rel_dev_double_vs_ball"] < bc["a_priori_bound_N600"]
          and abs(at["a_priori_relative_bound"] - ca.apriori_bound(5000)) < 1e-20
          and at["header"]["script_sha256"] == ca.sha256_of(HERE / "certify_atlas.py"))

    log(f"\n{'PASS' if not FAILS else 'FAIL'}  verify_coefficient ({len(FAILS)} failures, {time.time() - t0:.1f} s)")
    header = [f"# script: verify_coefficient.py",
              f"# sha256: {hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}",
              f"# uses certify_atlas.py sha256: {ca.sha256_of(HERE / 'certify_atlas.py')}",
              f"# input data/antimode.json sha256: {ca.sha256_of(HERE / 'data' / 'antimode.json')}",
              f"# date: {date.today().isoformat()}",
              f"# python {platform.python_version()}, numpy {np.__version__}, mpmath {mp.__version__}", ""]
    (HERE / "data" / "verify_coefficient_output.txt").write_text("\n".join(header + LINES) + "\n", encoding="utf-8")
    sys.exit(0 if not FAILS else 1)


if __name__ == "__main__":
    main()
