"""The preparation in the boundary layer and the big-jump zone (Theorem thm:preparation(c), (d),
Corollary cor:stationary) for three preparations, against the exact law.

Model: the zeta law f(n) = n^(-5/2)/zeta(5/2) for both signs (alpha_+ = alpha_- = 3/2, p = 1/2).
Preparations:
  fresh+      nu_+ = f, nu_- = 0 (the fresh plus start);
  stationary  nu_sigma = T_sigma/s, Q_sigma(N) = s^-1 sum_{d>=N} T(d);
  RV(0.3)     Sigma = + with probability 1/2 and then P(D >= n) = n^-0.3, Sigma = - with probability
              1/2 and then D uniform on {1, 2, 3}; so Q_+ is regularly varying with rho = 0.3 and the
              local regularity nu_+(n) ~ rho Q_+(n)/n of the paragraph after cor:stationary holds. Since
              rho < alpha_+ - 1, the preparation is visible in the boundary layer.
The exact law for a general preparation is computed by the run recursion with the first run
injected: an ordinary minus run starts at slot t+1 after a first plus run of length t (weight
nu_+(t)), and an ordinary plus run after a first minus run of length t (weight nu_-(t)). The
recursion is checked against certify_atlas.occupation for the fresh start and against the
first-run decomposition (Proposition prop:first-run) for the RV(0.3) preparation at small N.
The kernels Pi^-_m(b) (b minus slots among the first m of a fresh minus walk) are computed for all
m <= N from the same recursion.

Printed quantities, at N = 1200 and N = 2400:
  (d) for j in {1, 2, 3, 5, 10, 20}: P_N(N-j)/T_+(N), the ratio to the exact-defect form
      T_+(N) kappa_+(j) + B_N^-1 D^+_N(j), and the ratio to the regular form
      T_+(N) kappa_+(j) + nu_+(N)(1 + mu_+ u_-(j));
  (c) for ell = (k - pN)/((1-p)N) in {0.2, 0.5, 0.9}: P_N(k)/(G^nu_N(k) + Psi_N(k)),
      |P_N(k) - G^nu_N(k) - Psi_N(k)|/hatG_N(k), and P_N(k)/(G^nu_N(k) + nu_+(L)(1 + mu_+ u_-(N-k)));
  the stationary kernel: P_N(N-j)/T_+(N) against kappa^st_+(j) = (2/s)(1 + mu_+ u_-(j)).
Checks:
  1. the recursion for a general preparation (fresh start, first-run decomposition);
  2. mass one and the atoms P_N(N) = Q_+(N), P_N(0) = Q_-(N) for every preparation;
  3. the stationary kernels: kappa_+ of eq:kappa-prep equals p u_-(j) + 1/s, and kappa^st_+(j) -> 2/mu_-;
  4. the ratios of Corollary cor:stationary printed in Section 8 (1.0007, 1.0031, 1.0098 at j = 1, 2,
     5 and N = 2400) and the halving of each deviation from N = 1200 to N = 2400;
  5. for each preparation the largest deviation from 1 of the exact-defect ratio of (d) over the six
     values of j decreases from N = 1200 to N = 2400 and is below 0.15 (single values of j need not
     move monotonically, and the script notes those that do not).
The big-jump ratios are printed for information. Theorem thm:preparation(c) is a statement in the
double limit K -> infinity after N -> infinity, and no single N tests it.

Run from the paper folder:  py -I verify_preparation.py
Output: data/verify_preparation_output.txt and data/preparation_ratios.json (with the sha256 of this
script and the date). Exit status 1 if any check fails.
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
from flint import arb, ctx

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("certify_atlas", HERE / "certify_atlas.py")
ca = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ca)

NMAX = 2400
NS = (1200, 2400)
JS = (1, 2, 3, 5, 10, 20)
ELLS = (0.2, 0.5, 0.9)
RHO = 0.3
LINES = []
FAILS = []


def log(msg=""):
    print(msg, flush=True)
    LINES.append(msg)


def check(name, cond, detail=""):
    log(f"{'PASS' if cond else 'FAIL'}  {name}" + (f"  ({detail})" if detail else ""))
    if not cond:
        FAILS.append(name)


def run_prepared(fp, fm, nup, num, M):
    """A[t, k], B[t, k] for 0 <= k <= t <= M: an ordinary plus (minus) run starts at slot t+1 and the
    first t slots hold k plus slots. The first run is the preparation (nup, num); A[0] = B[0] = 0."""
    A = np.zeros((M + 1, M + 1))
    B = np.zeros((M + 1, M + 1))
    Ac = np.zeros((M + 1, M + 1))          # Ac[t, c] = A[t, t - c], c the number of minus slots
    fpr = fp[M:0:-1].copy()                # fpr[i] = f_+(M - i); contiguous copies keep matmul on BLAS
    fmr = fm[M:0:-1].copy()
    for t in range(1, M + 1):
        gp = fpr[M - t:M]                  # f_+(t - i), i = 0..t-1
        gm = fmr[M - t:M]
        Bc = gp @ Ac[:t, :t + 1]           # minus coordinates: a plus run keeps the minus count
        B[t, :t + 1] = Bc[t::-1]
        B[t, t] += nup[t]                  # first plus run of length t
        A[t, :t + 1] = gm @ B[:t, :t + 1]  # a minus run keeps the plus count
        A[t, 0] += num[t]                  # first minus run of length t
        Ac[t, :t + 1] = A[t, t::-1]
    return A, B


def law_prepared(A, B, Tp, Tm, Qp, Qm, N):
    """P_N(k), 0 <= k <= N: the final run is censored by the horizon, the first run by Q."""
    P = np.zeros(N + 1)
    for t in range(1, N):
        r = N - t
        P[r:N + 1] += A[t, :N + 1 - r] * Tp[r]
        P[:t + 1] += B[t, :t + 1] * Tm[r]
    P[N] += Qp
    P[0] += Qm
    return P


def kernels_minus(fp, fm, Tp, Tm, M):
    """K[m, c] = probability that a fresh minus walk has c minus slots among its first m slots."""
    A, B = run_prepared(fp, fm, np.zeros(M + 1), fm[:M + 1], M)
    Ac = np.zeros_like(A)
    for t in range(M + 1):
        Ac[t, :t + 1] = A[t, t::-1]
    idx = np.arange(M + 1)
    D = idx[:, None] - idx[None, :]        # m - t
    Top = np.where(D >= 1, Tp[np.clip(D, 0, M)], 0.0)
    Tom = np.where(D >= 1, Tm[np.clip(D, 0, M)], 0.0)
    term1 = Top @ Ac                       # final plus run: minus count unchanged, coordinate c
    term2 = Tom @ B                        # final minus run: plus count unchanged, coordinate k
    K = term1.copy()
    for m in range(1, M + 1):
        K[m, :m + 1] += term2[m, m::-1]    # k = m - c
        K[m, m] += Tm[m]                   # the first run covers the m slots
    K[0, 0] = 1.0
    return K


def tail_T_sum(N, alpha):
    """sum_{d>=N} T(d) for the zeta law, = [zeta(alpha, N) - (N-1) zeta(alpha+1, N)]/zeta(alpha+1)."""
    old = ctx.prec
    ctx.prec = 128
    a = arb(alpha)
    val = (a.zeta(arb(N)) - (N - 1) * (a + 1).zeta(arb(N))) / (a + 1).zeta()
    ctx.prec = old
    return float(val.mid())


def main():
    t_start = time.time()
    alpha = ca.ALPHA
    mu = ca.means()
    s = 2 * mu
    p = 0.5
    f, T = ca.law_arrays(NMAX + 2)
    u, v = ca.renewal(f, NMAX)
    log("verify_preparation.py: zeta law, alpha_+ = alpha_- = 3/2, three preparations")

    # preparations
    n = np.arange(NMAX + 1, dtype=float)
    preps = {}
    preps["fresh+"] = dict(nup=f[:NMAX + 1].copy(), num=np.zeros(NMAX + 1), pi_plus=1.0,
                           Qp=lambda N: T[N], Qm=lambda N: 0.0)
    nst = T[:NMAX + 1] / s
    nst[0] = 0.0
    preps["stationary"] = dict(nup=nst.copy(), num=nst.copy(), pi_plus=p,
                               Qp=lambda N: tail_T_sum(N, alpha) / s, Qm=lambda N: tail_T_sum(N, alpha) / s)
    nrv = np.zeros(NMAX + 1)
    nrv[1:] = 0.5 * (n[1:] ** -RHO - (n[1:] + 1) ** -RHO)
    mrv = np.zeros(NMAX + 1)
    mrv[1:4] = 0.5 / 3
    preps[f"RV({RHO})"] = dict(nup=nrv, num=mrv, pi_plus=0.5,
                               Qp=lambda N: 0.5 * N ** -RHO, Qm=lambda N: 0.0)

    t1 = time.time()
    K = kernels_minus(f, f, T, T, NMAX)
    log(f"kernels Pi^-_m(b), m <= {NMAX}: {time.time() - t1:.1f} s, max |row sum - 1| = "
        f"{np.max(np.abs(K[1:].sum(axis=1) - 1)):.1e}")

    # 1. the recursion for a general preparation
    t1 = time.time()
    Pfresh = ca.occupation(1200, f[:1202], T[:1202])
    A, B = run_prepared(f, f, preps["fresh+"]["nup"], preps["fresh+"]["num"], 1200)
    Pr = law_prepared(A, B, T, T, T[1200], 0.0, 1200)
    d1 = float(np.max(np.abs(Pr - Pfresh) / np.maximum(Pfresh, 1e-300)))
    # symmetry of the equal laws: Pi^-_m(c) = F^+_m(c)
    d2 = float(np.max(np.abs(K[1200, :1201] - Pfresh) / np.maximum(Pfresh, 1e-300)))
    # first-run decomposition for RV(0.3) at N <= 60
    Ms = 60
    A2, B2 = run_prepared(f, f, nrv, mrv, Ms)
    Ap, Bp = run_prepared(f, f, f[:Ms + 1], np.zeros(Ms + 1), Ms)
    d3 = 0.0
    for N in (7, 20, 45, 60):
        Qp, Qm = 0.5 * N ** -RHO, 0.0
        P = law_prepared(A2, B2, T, T, Qp, Qm, N)
        Pd = np.zeros(N + 1)
        Pd[N] += Qp
        Pd[0] += Qm
        for d in range(1, N):
            Fm_ = K[N - d, :N - d + 1][::-1]              # F^-_{N-d}(k) = Pi^-_{N-d}(N-d-k)
            Fp_ = law_prepared(Ap, Bp, T, T, T[N - d], 0.0, N - d)
            Pd[d:] += nrv[d] * Fm_
            Pd[:N - d + 1] += mrv[d] * Fp_
        d3 = max(d3, float(np.max(np.abs(P - Pd))))
    check("1. prepared recursion: fresh start = certify_atlas (N = 1200), Pi^- = F^+ (N = 1200), "
          "prop:first-run for RV(0.3) (N <= 60)", d1 < 1e-12 and d2 < 1e-12 and d3 < 1e-15,
          f"{d1:.1e}, {d2:.1e}, {d3:.1e}; {time.time() - t1:.1f} s")

    out = {}
    ok_mass = True
    for name, pr in preps.items():
        t1 = time.time()
        A, B = run_prepared(f, f, pr["nup"], pr["num"], NMAX)
        nup, num = pr["nup"], pr["num"]

        def kappa(j):
            return pr["pi_plus"] * u[j] * (j >= 1) + sum(num[d] * u[j - d] for d in range(1, j + 1))
        res = {}
        for N in NS:
            Qp, Qm = pr["Qp"](N), pr["Qm"](N)
            P = law_prepared(A, B, T, T, Qp, Qm, N)
            mass = float(abs(P.sum() - 1))
            ok_mass &= mass < 1e-12 and abs(P[N] - Qp) <= 1e-15 * max(Qp, 1e-300) + 1e-300 and P[0] == Qm
            bl = []
            for j in JS:
                Lam = sum(nup[N - m] * K[m, j] for m in range(1, (N + 1) // 2))   # 1 <= m < N/2
                exact = T[N] * kappa(j) + Lam
                regular = T[N] * kappa(j) + nup[N] * (1 + mu * u[j])
                bl.append(dict(j=j, P_over_T=P[N - j] / T[N], ratio_exact_defect=P[N - j] / exact,
                               ratio_regular=P[N - j] / regular))
            bj = []
            for ell in ELLS:
                k = int(round(p * N + (1 - p) * ell * N))
                L = (k - p * N) / (1 - p)
                Lf = int(np.floor(L))
                j = N - k
                Gnu = (N - L) / mu * f[Lf] + T[Lf] * kappa(j)
                Psi = sum(nup[d] * K[N - d, j] for d in range(int(np.ceil(L / 2)), N) if N - d >= j)
                Ghat = (N / L) * T[Lf]
                reg = nup[Lf] * (1 + mu * u[j])
                bj.append(dict(ell=ell, k=k, ratio_G_Psi=P[k] / (Gnu + Psi), err_over_Ghat=abs(P[k] - Gnu - Psi) / Ghat,
                               ratio_G_regular=P[k] / (Gnu + reg), Psi_over_Ghat=Psi / Ghat))
            res[N] = dict(mass_defect=mass, atom_ratio=P[N] / Qp if Qp else None, boundary=bl, bigjump=bj,
                          P_end=[float(P[N - j]) for j in range(0, 41)])
        out[name] = res
        log(f"\n== {name} ({time.time() - t1:.1f} s)")
        for N in NS:
            r = res[N]
            log(f" N={N}: mass defect {r['mass_defect']:.1e}, P_N(N)/Q_+(N) = {r['atom_ratio']:.15f}")
            log("   j   P/T_+(N)   P/[T kappa + L/B]   P/[T kappa + nu(N)(1+mu u)]")
            for b in r["boundary"]:
                log(f"  {b['j']:2d} {b['P_over_T']:10.4f} {b['ratio_exact_defect']:12.4f} {b['ratio_regular']:14.4f}")
            log("   ell   k     P/(Gnu+Psi)  |P-Gnu-Psi|/hatG  P/(Gnu+nu(L)(1+mu u))  Psi/hatG")
            for b in r["bigjump"]:
                log(f"  {b['ell']:.1f} {b['k']:5d} {b['ratio_G_Psi']:10.4f} {b['err_over_Ghat']:12.4f} "
                    f"{b['ratio_G_regular']:14.4f} {b['Psi_over_Ghat']:16.4f}")
    check("2. mass one, P_N(N) = Q_+(N) and P_N(0) = Q_-(N) for the three preparations, N = 1200, 2400", ok_mass)

    # 3. the stationary kernels
    nst_ = preps["stationary"]["num"]
    kp = np.array([p * u[j] + sum(nst_[d] * u[j - d] for d in range(1, j + 1)) for j in range(1, 401)])
    dk = float(np.max(np.abs(kp - (p * u[1:401] + 1 / s))))
    kst = 2 / s * (1 + mu * u)
    check("3. eq:kappa-prep for the stationary start equals p u_-(j) + 1/s (j <= 400), "
          "and kappa^st_+(j) = (2/s)(1 + mu_+ u_-(j)) tends to 2/mu_-",
          dk < 1e-14 and abs(kst[NMAX] - 2 / mu) < abs(kst[100] - 2 / mu) < abs(kst[10] - 2 / mu),
          f"max diff {dk:.1e}; kappa^st at j = 10, 100, 2400: {kst[10]:.4f}, {kst[100]:.4f}, {kst[NMAX]:.4f}; "
          f"2/mu = {2 / mu:.4f}")

    # 4. the printed ratios of Corollary cor:stationary
    st = out["stationary"]
    rat = {N: {b["j"]: b["P_over_T"] / kst[b["j"]] for b in st[N]["boundary"]} for N in NS}
    log("   stationary P_N(N-j)/(T_+(N) kappa^st(j)): " + "; ".join(
        f"N={N}: " + ", ".join(f"j={j}: {rat[N][j]:.5f}" for j in (1, 2, 5)) for N in NS))
    halves = [(rat[2400][j] - 1) / (rat[1200][j] - 1) for j in (1, 2, 5)]
    check("4a. cor:stationary(c): ratio 1.0007, 1.0031, 1.0098 at j = 1, 2, 5, N = 2400",
          [f"{rat[2400][j]:.4f}" for j in (1, 2, 5)] == ["1.0007", "1.0031", "1.0098"])
    check("4b. each deviation at N = 2400 is about half of its value at N = 1200 (ratio in [0.4, 0.6])",
          all(0.4 <= h <= 0.6 for h in halves), ", ".join(f"{h:.3f}" for h in halves))

    # 5. the exact-defect ratio in the boundary layer: the largest deviation over j decreases
    ok5 = True
    worst = {}
    for name in out:
        e = {N: max(abs(b["ratio_exact_defect"] - 1) for b in out[name][N]["boundary"]) for N in NS}
        worst[name] = e
        ok5 &= e[2400] < e[1200] and e[2400] < 0.15
        for b1, b2 in zip(out[name][1200]["boundary"], out[name][2400]["boundary"]):
            e1, e2 = abs(b1["ratio_exact_defect"] - 1), abs(b2["ratio_exact_defect"] - 1)
            if e2 >= e1:
                log(f"   note: {name}, j = {b1['j']}: deviation {e1:.4f} at N = 1200 and {e2:.4f} at N = 2400")
    check("5. thm:preparation(d): for each preparation the largest deviation of the exact-defect ratio from 1 "
          "over j in {1,2,3,5,10,20} decreases from N = 1200 to 2400 and is below 0.15", ok5,
          "; ".join(f"{k}: {v[1200]:.4f} -> {v[2400]:.4f}" for k, v in worst.items()))

    rec = {"header": {"script": "verify_preparation.py",
                      "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                      "uses": {"certify_atlas.py": ca.sha256_of(HERE / "certify_atlas.py")},
                      "date": date.today().isoformat(),
                      "model": "zeta law for both signs, alpha = 1.5; preparations fresh+, stationary, RV(0.3)"},
           "mu": mu, "s": s, "results": {k: {str(N): v for N, v in r.items()} for k, r in out.items()},
           "stationary_kernel": [float(x) for x in kst[:41]]}
    (HERE / "data" / "preparation_ratios.json").write_text(json.dumps(rec, indent=1))
    log(f"\n{'PASS' if not FAILS else 'FAIL'}  verify_preparation ({len(FAILS)} failures, {time.time() - t_start:.1f} s)")
    header = [f"# script: verify_preparation.py",
              f"# sha256: {rec['header']['script_sha256']}",
              f"# uses certify_atlas.py sha256: {rec['header']['uses']['certify_atlas.py']}",
              f"# date: {date.today().isoformat()}",
              f"# python {platform.python_version()}, numpy {np.__version__}", ""]
    (HERE / "data" / "verify_preparation_output.txt").write_text("\n".join(header + LINES) + "\n", encoding="utf-8")
    sys.exit(0 if not FAILS else 1)


if __name__ == "__main__":
    main()
