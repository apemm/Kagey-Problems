"""Exposure count A_N of a switchback that switches arm at every regeneration of a slotted Geo/G/1
queue, against the predictions of Paper F.

Arms. Treatment (plus) and control (minus) differ only in the arrival probability: service is
zeta(alpha+1) in both arms, and the loads are rho_+ and rho_-. The run laws are the cycle laws
f_+ = f_C(rho_+) and f_- = f_C(rho_-) of 04_cycle_law.py. The experiment switches arm at every
regeneration (empty epoch), so the cycles are independent and A_N (treated slots among the first N)
is exactly the occupation count of Paper F.

Starts. fresh   : the experiment starts on an empty system in the treatment arm (nu_+ = f_+).
        random  : the experiment starts at a typical time of a long-running switchback
                  (stationary initial run nu_sigma = T_sigma/s).
        ctrl    : the experiment starts at a typical time of a system that ran in control only,
                  and the cycle in progress stays in control (nu_- = T_-/mu_-, nu_+ = 0).

Checks and printed comparisons (labels are those of Paper F):
  0. the exact law is a probability law; atoms P_N(N) = T_+(N) (fresh) and Q_sigma(N) (random);
  1. Monte Carlo of the queue with switching at regenerations against the exact law (N = 200);
  2. bulk (thm:bulk): B_N P_N(k) against the profile h at a few points, quantiles of (A_N - pN)/B_N;
  3. big jump (thm:bigjump, cor:infinite-density, cor:stationary(b)): P_N(vN)/T_+(N);
  4. severe imbalance (Corollary E2 of 04_exposure_queues.md): P(A_N >= (1-eps)N);
  5. no switch (Corollary E3): fresh T_+(N) + 0, random Q_+(N) + Q_-(N), and the factor N/(s(alpha-1));
  6. global mode (thm:mode(d), golden ratio) for alpha = 1.5 and 1.8 under the random and ctrl starts;
  7. number of modes of the fresh law (thm:mode-count, cor:logconvex-three).

Run:  py -I 04_exposure_law.py      Output: 04_exposure_law_output.txt next to this script.
"""
import importlib.util
import sys
import time
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.special import gamma as Gamma, zeta

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("cyc", HERE / "04_cycle_law.py")
cyc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cyc)

LINES = []
FAILS = []


def log(msg=""):
    print(msg, flush=True)
    LINES.append(msg)


def check(name, cond, detail=""):
    log(f"{'PASS' if cond else 'FAIL'}  {name}" + (f"  ({detail})" if detail else ""))
    if not cond:
        FAILS.append(name)


class Model:
    def __init__(self, alpha, rho_p, rho_m, nmax):
        self.alpha, self.rho_p, self.rho_m = alpha, rho_p, rho_m
        self.lam_p, self.lam_m = cyc.lam_of(alpha, rho_p), cyc.lam_of(alpha, rho_m)
        self.fp = cyc.cycle_pmf(alpha, self.lam_p, nmax)
        self.fm = cyc.cycle_pmf(alpha, self.lam_m, nmax)
        self.fp[0] = self.fm[0] = 0.0
        # T(n) = P(C >= n), n = 0..nmax
        self.Tp = 1.0 - np.concatenate(([0.0], np.cumsum(self.fp[:-1])))
        self.Tm = 1.0 - np.concatenate(([0.0], np.cumsum(self.fm[:-1])))
        self.Tp[0] = self.Tm[0] = 1.0
        self.mup, self.mum = 1 / (1 - rho_p), 1 / (1 - rho_m)
        self.s = self.mup + self.mum
        self.p = self.mup / self.s
        a = alpha
        self.cp = self.lam_p * (1 - rho_p) ** (-a - 1) / (a * zeta(a + 1))   # T_+(n) ~ cp n^-a
        self.cm = self.lam_m * (1 - rho_m) ** (-a - 1) / (a * zeta(a + 1))

    def Qtail(self, T, mu, N):
        """sum_{d >= N} T(d) = mu - sum_{d=1}^{N-1} T(d), exact since sum_{d>=1} T(d) = E C = mu."""
        return mu - T[1:N].sum()

    def law(self, N, start):
        fp, fm, Tp, Tm = self.fp, self.fm, self.Tp, self.Tm
        nup = np.zeros(N + 1)
        num = np.zeros(N + 1)
        a00 = 0.0
        Qp = Qm = 0.0
        if start == "fresh":
            a00 = 1.0
        elif start == "random":
            nup[1:] = Tp[1:N + 1] / self.s
            num[1:] = Tm[1:N + 1] / self.s
            Qp = self.Qtail(Tp, self.mup, N) / self.s
            Qm = self.Qtail(Tm, self.mum, N) / self.s
        elif start == "ctrl":
            num[1:] = Tm[1:N + 1] / self.mum
            Qm = self.Qtail(Tm, self.mum, N) / self.mum
        AC = np.zeros((N + 1, N + 1))     # AC[t, c]: plus run starts at t+1, c minus slots before
        A = np.zeros((N + 1, N + 1))      # A[t, k]: same event, k plus slots before
        B = np.zeros((N + 1, N + 1))      # B[t, k]: minus run starts at t+1, k plus slots before
        AC[0, 0] = A[0, 0] = a00
        fpr = fp[N:0:-1].copy()           # fpr[i] = f_+(N - i)
        fmr = fm[N:0:-1].copy()
        for t in range(1, N + 1):
            gp = fpr[N - t:N]             # f_+(t - i), i = 0..t-1
            gm = fmr[N - t:N]
            Bc = gp @ AC[:t, :t + 1]      # minus count c is kept by a plus run
            B[t, :t + 1] = Bc[t::-1]
            B[t, t] += nup[t]
            A[t, :t + 1] = gm @ B[:t, :t + 1]
            A[t, 0] += num[t]
            AC[t, :t + 1] = A[t, t::-1]
        P = np.zeros(N + 1)
        for t in range(0, N):
            r = N - t
            P[r:N + 1] += A[t, :N + 1 - r] * Tp[r]     # final plus run of r slots
            P[:t + 1] += B[t, :t + 1] * Tm[r]          # final minus run of r slots
        P[N] += Qp
        P[0] += Qm
        return P, Qp, Qm

    def scales(self, N):
        a = self.alpha
        bp = (self.cp * N / self.s) ** (1 / a)
        bm = (self.cm * N / self.s) ** (1 / a)
        BN = max(bp, bm)
        return bp / BN, bm / BN, BN

    def profile(self, N):
        """density h_N of (1-p) th_+ Z_+ - p th_- Z_-, E e^{itZ} = exp(K (-it)^a), K = -Gamma(1-a)."""
        a = self.alpha
        K = -Gamma(1 - a)
        thp, thm, _ = self.scales(N)
        cpl = K * ((1 - self.p) * thp) ** a
        cmi = K * (self.p * thm) ** a

        def phi(t):  # t > 0
            z1 = (t ** a) * np.exp(-1j * np.pi * a / 2)   # (-it)^a
            z2 = (t ** a) * np.exp(1j * np.pi * a / 2)    # (it)^a
            return np.exp(cpl * z1 + cmi * z2)

        def h(x):
            val, _ = quad(lambda t: (np.exp(-1j * t * x) * phi(t)).real, 0, np.inf, limit=400)
            return val / np.pi
        return h


def local_maxima(P):
    """strict-plateau local maxima count of a sequence (plateaus counted once)."""
    x = P
    count = 0
    n = len(x)
    i = 0
    while i < n:
        j = i
        while j + 1 < n and x[j + 1] == x[i]:
            j += 1
        left = x[i - 1] if i > 0 else -np.inf
        right = x[j + 1] if j + 1 < n else -np.inf
        if x[i] > left and x[i] > right:
            count += 1
        i = j + 1
    return count


def main():
    t0 = time.time()
    rng = np.random.default_rng(31415)
    NS = (1000, 2000, 4000)
    M = Model(1.5, 0.6, 0.4, max(NS) + 2)
    a = M.alpha
    log(f"alpha = {a}, rho_+ = {M.rho_p}, rho_- = {M.rho_m}, lam_+ = {M.lam_p:.6f}, lam_- = {M.lam_m:.6f}")
    log(f"mu_+ = {M.mup:.4f}, mu_- = {M.mum:.4f}, s = {M.s:.4f}, p = {M.p:.4f}, "
        f"T_+ ~ {M.cp:.4f} n^-a, T_- ~ {M.cm:.4f} n^-a")

    # 1. Monte Carlo of the queue with switching at regenerations
    N0 = 200
    P0, _, _ = M.law(N0, "fresh")
    R = 300000
    V = np.zeros(R, dtype=np.int64)
    arm = np.ones(R, dtype=bool)          # True = treatment
    cnt = np.zeros(R, dtype=np.int64)
    for _ in range(N0):
        cnt += arm
        lam = np.where(arm, M.lam_p, M.lam_m)
        arr = rng.random(R) < lam
        W = np.zeros(R, dtype=np.int64)
        W[arr] = rng.zipf(a + 1.0, arr.sum())
        V = np.maximum(V - 1, 0) + W
        arm = np.where(V == 0, ~arm, arm)  # switch at every empty epoch
    emp = np.bincount(cnt, minlength=N0 + 1) / R
    edges = [1, 20, 60, 100, 110, 120, 130, 140, 160, 180, 199, 200, 201]
    chi2 = 0.0
    log("   Monte Carlo, fresh treatment start, N = 200, 300000 queues")
    for lo, hi in zip(edges[:-1], edges[1:]):
        e = P0[lo:hi].sum()
        o = emp[lo:hi].sum()
        chi2 += R * (o - e) ** 2 / e
        log(f"   A_N in [{lo:3d},{hi:3d}): exact {e:.5f}  simulated {o:.5f}")
    check("simulated queue matches the exact law (chi-square, 11 df, < 31.26 = 0.999 quantile)", chi2 < 31.26,
          f"chi2 = {chi2:.1f}")

    for N in NS:
        log(f"\n=== N = {N}")
        Pf, _, _ = M.law(N, "fresh")
        Pr, Qp, Qm = M.law(N, "random")
        Tp, Tm = M.Tp, M.Tm
        check("fresh law has mass 1", abs(Pf.sum() - 1) < 1e-9, f"{Pf.sum():.12f}")
        check("random-start law has mass 1", abs(Pr.sum() - 1) < 1e-9, f"{Pr.sum():.12f}")
        check("fresh atoms P_N(N) = T_+(N), P_N(0) = 0", abs(Pf[N] / Tp[N] - 1) < 1e-9 and Pf[0] == 0.0)
        # 2. bulk
        thp, thm, BN = M.scales(N)
        h = M.profile(N)
        log(f"   B_N = {BN:.3f} (theta_+ = {thp:.3f}, theta_- = {thm:.3f}), pN = {M.p * N:.1f}")
        log("   x      B_N P_N fresh   B_N P_N random   h(x)")
        for x in (-2.0, -1.0, 0.0, 1.0, 2.0):
            k = int(round(M.p * N + x * BN))
            xx = (k - M.p * N) / BN
            log(f"   {xx:+.3f}  {BN * Pf[k]:.5f}         {BN * Pr[k]:.5f}          {h(xx):.5f}")
        cdf = np.cumsum(Pf)
        qs = []
        for q in (0.05, 0.25, 0.5, 0.75, 0.95):
            k = int(np.searchsorted(cdf, q))
            qs.append((k - M.p * N) / BN)
        log("   quantiles 5/25/50/75/95% of (A_N - pN)/B_N, fresh: " + ", ".join(f"{v:+.3f}" for v in qs))
        # 3. big jump
        log("   v      ell    P_N/T_+(N) fresh   I_+(v)     random    I_+(v)+ell^-a/mu_-")
        for ell in (0.3, 0.6, 0.9):
            v = M.p + ell * (1 - M.p)
            k = int(np.floor(v * N))
            I = (a * (1 - ell) * ell ** (-a - 1) + ell ** (-a)) / M.mum
            log(f"   {v:.3f}  {ell:.1f}   {Pf[k] / Tp[N]:9.4f}          {I:8.4f}   {Pr[k] / Tp[N]:8.4f}  "
                f"{I + ell ** (-a) / M.mum:8.4f}")
        # 4. severe imbalance: control gets fewer than eps N slots
        log("   eps   P(A_N >= (1-eps)N) fresh   prediction   ratio | random   prediction   ratio")
        for eps in (0.05, 0.1, 0.2):
            k0 = int(np.ceil((1 - eps) * N))
            le = 1 - eps / (1 - M.p)
            pf = Pf[k0:].sum()
            pr = Pr[k0:].sum()
            predf = N * Tp[N] * eps * le ** (-a) / M.mum
            predr = predf + N * Tp[N] * le ** (1 - a) / (M.s * (a - 1))
            log(f"   {eps:.2f}  {pf:.4e}               {predf:.4e}   {pf / predf:.3f} | {pr:.4e}  {predr:.4e}  "
                f"{pr / predr:.3f}")
        # minus end: treatment gets fewer than eps N slots
        for eps in (0.1,):
            k1 = int(np.floor(eps * N))
            le = 1 - eps / M.p
            pf = Pf[:k1 + 1].sum()
            predf = N * Tm[N] * eps * le ** (-a) / M.mup
            log(f"   P(A_N <= {eps}N) fresh {pf:.4e}  prediction {predf:.4e}  ratio {pf / predf:.3f}")
        # 5. no switch
        nsf = Pf[N] + Pf[0]
        nsr = Pr[N] + Pr[0]
        pred_ratio = N * (Tp[N] + Tm[N]) / (M.s * (a - 1)) / Tp[N]
        log(f"   no switch: fresh {nsf:.4e} (= T_+(N)), random {nsr:.4e} (Q_+ = {Qp:.4e}, Q_- = {Qm:.4e})")
        log(f"   ratio random/fresh {nsr / nsf:.2f}; asymptotic N(T_+ + T_-)/(s(alpha-1)T_+) = {pred_ratio:.2f}; "
            f"N/(s(alpha-1)) = {N / (M.s * (a - 1)):.2f}")
        # 7. number of modes, fresh start
        nm = local_maxima(Pf)
        um = np.zeros(60)
        um[0] = 1.0
        for j in range(1, 60):
            um[j] = np.dot(M.fm[1:j + 1], um[j - 1::-1][:j])
        check(f"fresh law has exactly 3 modes at N = {N}", nm == 3, f"{nm} local maxima")
        check("u_- strictly decreasing on 1 <= j < 60", bool(np.all(np.diff(um[1:]) < 0)))

    # 6. golden ratio: global mode under the random and ctrl starts
    log("\n=== global mode (thm:mode(d)); 'endpoint' means the most likely value of A_N is 0 or N")
    for alpha in (1.5, 1.8):
        Mg = Model(alpha, 0.6, 0.4, max(NS) + 2) if alpha != 1.5 else M
        for N in NS:
            for start in ("random", "ctrl"):
                P, _, _ = Mg.law(N, start)
                inner = P[1:N].max()
                endv = max(P[0], P[N])
                where = "endpoint" if endv > inner else "interior"
                log(f"   alpha = {alpha}, N = {N}, {start:6s}: max(P_N(0),P_N(N)) / max interior = "
                    f"{endv / inner:.3f}  -> {where}")
                expect = "endpoint" if alpha < (1 + 5 ** 0.5) / 2 else "interior"
                check(f"golden-ratio prediction ({expect}) holds, alpha={alpha}, N={N}, {start}", where == expect)
    log(f"\ntime {time.time() - t0:.1f} s; {'all checks passed' if not FAILS else 'FAILED: ' + ', '.join(FAILS)}")
    (HERE / "04_exposure_law_output.txt").write_text("\n".join(LINES) + "\n", encoding="utf-8", newline="\n")
    sys.exit(1 if FAILS else 0)


if __name__ == "__main__":
    main()
