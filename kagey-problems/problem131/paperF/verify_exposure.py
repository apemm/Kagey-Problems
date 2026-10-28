"""The cycle law of the slotted queue (Proposition prop:cycle) and the exposure law of the switchback
(Corollaries cor:exposure-bulk, cor:exposure-tail, cor:exposure-mode) against exact computations.

Queue: in each slot a customer arrives with probability lambda and brings Y slots of work, with the zeta
law P(Y = n) = n^(-alpha-1)/zeta(alpha+1). The workload is V_t = max(V_{t-1} - 1, 0) + W_t, a regeneration
is a slot that ends empty, and the cycle C is the number of slots between regenerations. The two arms
share Y and have loads rho_+ = 0.6 and rho_- = 0.4; alpha = 1.5, and alpha = 1.8 for the golden-ratio check.

Part A, the cycle law. The mass function from the cyclic lemma eq:cyclic, f_C(n) = P(U_n = n-1)/n, with U_n
by FFT convolution, checked against a dynamic program on the workload itself (n <= 300) and against direct
convolution (n <= 1000); mass one and E C = 1/(1-rho); the ratios f_C(n)/[lambda (1-rho)^(-alpha-1) f_Y(n)]
of Proposition prop:cycle(a); n Delta f_C/f_C against -(alpha+1) and n^2 Delta^2 f_C/f_C against
(alpha+1)(alpha+2) (part (b)); strict log-convexity of f_C on 2 <= n < 2^14 (a finite check, not a proof);
a Monte Carlo of the queue.
Part B, the exposure law, by the run recursion eq:run-recursion with the initial run injected, for the
fresh, random-time and control-only starts at N = 1000, 2000, 4000: a simulation of the switching queue
at N = 200 (chi-square); B_N P_N(k) against the profile h; P_N(vN)/T_+(N) against I_+(v) and the stationary
form; P(N - A_N < eps N) against Corollary cor:exposure-tail(a); the no-switch probabilities and the factor
of Corollary cor:exposure-tail(b); the global mode (Corollary cor:exposure-mode(b)); the number of modes
of the fresh law (Corollary cor:exposure-mode(c)).

Run from the paper folder:  py -I verify_exposure.py      (about four minutes)
Output: data/verify_exposure_output.txt (with the sha256 of this script).
"""
from datetime import date
from pathlib import Path
import hashlib
import platform
import sys
import time

import numpy as np
from scipy.integrate import quad
from scipy.special import gamma as Gamma, zeta

HERE = Path(__file__).resolve().parent
LINES = []
FAILS = []
PHI = (1 + 5 ** 0.5) / 2


def log(msg=""):
    print(msg, flush=True)
    LINES.append(msg)


def check(name, cond, detail=""):
    if not cond:
        FAILS.append(name)
    log(f"{'PASS' if cond else 'FAIL'}  {name}" + (f"  ({detail})" if detail else ""))


# ---------------------------------------------------------------- Part A: the cycle law

def work_pmf(alpha, lam, M):
    n = np.arange(1, M + 1, dtype=float)
    fW = np.zeros(M + 1)
    fW[0] = 1.0 - lam
    fW[1:] = lam * n ** (-alpha - 1.0) / zeta(alpha + 1.0)
    return fW


def lam_of(alpha, rho):
    return rho * zeta(alpha + 1.0) / zeta(alpha)


def cycle_pmf(alpha, lam, nmax):
    """f_C(1..nmax) by the cyclic lemma; U_n by repeated FFT convolution truncated to [0, nmax], which is
    exact for the values used since U_n = n - 1 <= nmax."""
    fW = work_pmf(alpha, lam, nmax)
    size = 1
    while size < 2 * (nmax + 1):
        size *= 2
    FW = np.fft.rfft(fW, size)
    u = np.zeros(nmax + 1)
    u[0] = 1.0
    fC = np.zeros(nmax + 1)
    for n in range(1, nmax + 1):
        u = np.fft.irfft(np.fft.rfft(u, size) * FW, size)[:nmax + 1]
        np.maximum(u, 0.0, out=u)
        fC[n] = u[n - 1] / n
    return fC


def cycle_pmf_direct(alpha, lam, nmax):
    fW = work_pmf(alpha, lam, nmax)
    u = np.zeros(nmax + 1)
    u[0] = 1.0
    fC = np.zeros(nmax + 1)
    for n in range(1, nmax + 1):
        u = np.convolve(u, fW)[:nmax + 1]
        fC[n] = u[n - 1] / n
    return fC


def cycle_pmf_queue_dp(alpha, lam, nmax):
    """P(C = n) from the workload recursion itself."""
    fW = work_pmf(alpha, lam, nmax + 1)
    fC = np.zeros(nmax + 1)
    fC[1] = fW[0]
    dist = fW[1:nmax + 1].copy()
    for n in range(2, nmax + 1):
        new = np.convolve(dist, fW)[:nmax + 1]
        fC[n] = new[0]
        dist = new[1:nmax + 1]
        dist[max(0, nmax - n):] = 0.0
    return fC


def part_a(rng):
    for alpha, rho in ((1.5, 0.4), (1.5, 0.6), (1.8, 0.5)):
        lam = lam_of(alpha, rho)
        log(f"=== cycle law: alpha = {alpha}, rho = {rho}, lambda = {lam:.6f}")
        dp = cycle_pmf_queue_dp(alpha, lam, 300)
        fC_small = cycle_pmf_direct(alpha, lam, 1000)
        rel = np.max(np.abs(dp[1:] - fC_small[1:301]) / fC_small[1:301])
        check("A1. cyclic lemma against the workload dynamic program, n <= 300", rel < 1e-10, f"max rel diff {rel:.1e}")
        nmax = 2 ** 14
        fC = cycle_pmf(alpha, lam, nmax)
        rel = np.max(np.abs(fC[1:1001] - fC_small[1:]) / fC_small[1:])
        check("A2. FFT against direct convolution, n <= 1000", rel < 1e-8, f"max rel diff {rel:.1e}")
        cst = lam * (1 - rho) ** (-alpha - 1) / zeta(alpha + 1)
        n = np.arange(nmax + 1, dtype=float)
        mass = fC[1:].sum() + cst * nmax ** (-alpha) / alpha
        mean = (n[1:] * fC[1:]).sum() + cst * nmax ** (1 - alpha) / (alpha - 1)
        check("A3. total mass one (asymptotic tail beyond 2^14)", abs(mass - 1) < 1e-6, f"{mass:.10f}")
        check("A4. E C = 1/(1-rho) (asymptotic tail beyond 2^14)", abs(mean * (1 - rho) - 1) < 1e-3,
              f"E C = {mean:.6f}, 1/(1-rho) = {1 / (1 - rho):.6f}")
        fW = work_pmf(alpha, lam, nmax)
        log("     n     f_C(n)/[lambda (1-rho)^(-a-1) f_Y(n)]   f_C(n)/f_W((1-rho)n)   n Df/f    n^2 D2f/f")
        for k in (2 ** e for e in range(5, 15)):
            m = int(round((1 - rho) * k))
            d1 = k * (fC[k + 1] - fC[k]) / fC[k] if k + 1 <= nmax else float('nan')
            d2 = k * k * (fC[k + 1] - 2 * fC[k] + fC[k - 1]) / fC[k] if k + 1 <= nmax else float('nan')
            log(f"  {k:6d}   {fC[k] / (cst * k ** (-alpha - 1)):.6f}                              "
                f"{fC[k] / fW[m]:.6f}            {d1:8.4f}  {d2:9.4f}")
        log(f"           limits: 1, 1, {-(alpha + 1):.4f}, {(alpha + 1) * (alpha + 2):.4f}")
        r_last = fC[nmax] / (cst * nmax ** (-alpha - 1))
        check("A5. ratio to the constant within 1% at n = 2^14", abs(r_last - 1) < 0.01, f"{r_last:.4f}")
        k = 2 ** 13
        d1 = k * (fC[k + 1] - fC[k]) / fC[k]
        d2 = k * k * (fC[k + 1] - 2 * fC[k] + fC[k - 1]) / fC[k]
        check("A6. (LD) and (LD2) constants within 1% at n = 2^13", abs(d1 / (alpha + 1) + 1) < 0.01 and
              abs(d2 / ((alpha + 1) * (alpha + 2)) - 1) < 0.01, f"{d1:.4f}, {d2:.4f}")
        lc = fC[2:nmax] ** 2 - fC[1:nmax - 1] * fC[3:nmax + 1]
        check("A7. f_C strictly log-convex on 2 <= n < 2^14 (finite check)", bool(np.all(lc < 0)),
              f"max relative f(n)^2 - f(n-1)f(n+1): {np.max(lc / fC[2:nmax] ** 2):.2e}")
        R = 400000
        lengths = np.zeros(R, dtype=np.int64)
        V = np.zeros(R, dtype=np.int64)
        alive = np.ones(R, dtype=bool)
        t = 0
        while alive.any() and t < 2000:
            t += 1
            idx = np.nonzero(alive)[0]
            arr = rng.random(idx.size) < lam
            W = np.zeros(idx.size, dtype=np.int64)
            W[arr] = rng.zipf(alpha + 1.0, arr.sum())
            V[idx] = np.maximum(V[idx] - 1, 0) + W
            done = V[idx] == 0
            lengths[idx[done]] = t
            alive[idx[done]] = False
        lengths = lengths[lengths > 0]
        worst = 0.0
        for k in (1, 2, 3, 5, 10, 20, 50):
            emp = np.mean(lengths == k) * lengths.size / R
            se = np.sqrt(fC[k] * (1 - fC[k]) / R)
            worst = max(worst, abs((emp - fC[k]) / se))
        check(f"A8. Monte Carlo of {R} cycles agrees with the exact law (|z| < 4.5 at 7 points)", worst < 4.5,
              f"max |z| {worst:.2f}")
        log("")


# ---------------------------------------------------------------- Part B: the exposure law

class Model:
    def __init__(self, alpha, rho_p, rho_m, nmax):
        self.alpha, self.rho_p, self.rho_m = alpha, rho_p, rho_m
        self.lam_p, self.lam_m = lam_of(alpha, rho_p), lam_of(alpha, rho_m)
        self.fp = cycle_pmf(alpha, self.lam_p, nmax)
        self.fm = cycle_pmf(alpha, self.lam_m, nmax)
        self.fp[0] = self.fm[0] = 0.0
        self.Tp = 1.0 - np.concatenate(([0.0], np.cumsum(self.fp[:-1])))
        self.Tm = 1.0 - np.concatenate(([0.0], np.cumsum(self.fm[:-1])))
        self.Tp[0] = self.Tm[0] = 1.0
        self.mup, self.mum = 1 / (1 - rho_p), 1 / (1 - rho_m)
        self.s = self.mup + self.mum
        self.p = self.mup / self.s
        a = alpha
        self.cp = self.lam_p * (1 - rho_p) ** (-a - 1) / (a * zeta(a + 1))
        self.cm = self.lam_m * (1 - rho_m) ** (-a - 1) / (a * zeta(a + 1))

    def Qtail(self, T, mu, N):
        return mu - T[1:N].sum()

    def law(self, N, start):
        """The exact law by the run recursion eq:run-recursion with the initial run injected."""
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
        AC = np.zeros((N + 1, N + 1))
        A = np.zeros((N + 1, N + 1))
        B = np.zeros((N + 1, N + 1))
        AC[0, 0] = A[0, 0] = a00
        fpr = fp[N:0:-1].copy()
        fmr = fm[N:0:-1].copy()
        for t in range(1, N + 1):
            gp = fpr[N - t:N]
            gm = fmr[N - t:N]
            Bc = gp @ AC[:t, :t + 1]
            B[t, :t + 1] = Bc[t::-1]
            B[t, t] += nup[t]
            A[t, :t + 1] = gm @ B[:t, :t + 1]
            A[t, 0] += num[t]
            AC[t, :t + 1] = A[t, t::-1]
        P = np.zeros(N + 1)
        for t in range(0, N):
            r = N - t
            P[r:N + 1] += A[t, :N + 1 - r] * Tp[r]
            P[:t + 1] += B[t, :t + 1] * Tm[r]
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
        a = self.alpha
        K = -Gamma(1 - a)
        thp, thm, _ = self.scales(N)
        cpl = K * ((1 - self.p) * thp) ** a
        cmi = K * (self.p * thm) ** a

        def phi(t):
            return np.exp(cpl * (t ** a) * np.exp(-1j * np.pi * a / 2) + cmi * (t ** a) * np.exp(1j * np.pi * a / 2))

        def h(x):
            val, _ = quad(lambda t: (np.exp(-1j * t * x) * phi(t)).real, 0, np.inf, limit=400)
            return val / np.pi
        return h


def local_maxima(x):
    count, n, i = 0, len(x), 0
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


def part_b(rng):
    NS = (1000, 2000, 4000)
    M = Model(1.5, 0.6, 0.4, max(NS) + 2)
    a = M.alpha
    log(f"=== exposure law: alpha = {a}, rho_+ = {M.rho_p}, rho_- = {M.rho_m}, lambda_+ = {M.lam_p:.6f}, "
        f"lambda_- = {M.lam_m:.6f}")
    log(f"mu_+ = {M.mup:.4f}, mu_- = {M.mum:.4f}, s = {M.s:.4f}, p = {M.p:.4f}, "
        f"T_+(n) ~ {M.cp:.4f} n^-a, T_-(n) ~ {M.cm:.4f} n^-a")
    N0 = 200
    P0, _, _ = M.law(N0, "fresh")
    R = 300000
    V = np.zeros(R, dtype=np.int64)
    arm = np.ones(R, dtype=bool)
    cnt = np.zeros(R, dtype=np.int64)
    for _ in range(N0):
        cnt += arm
        lam = np.where(arm, M.lam_p, M.lam_m)
        arr = rng.random(R) < lam
        W = np.zeros(R, dtype=np.int64)
        W[arr] = rng.zipf(a + 1.0, arr.sum())
        V = np.maximum(V - 1, 0) + W
        arm = np.where(V == 0, ~arm, arm)
    emp = np.bincount(cnt, minlength=N0 + 1) / R
    edges = [1, 20, 60, 100, 110, 120, 130, 140, 160, 180, 199, 200, 201]
    chi2 = 0.0
    for lo, hi in zip(edges[:-1], edges[1:]):
        e = P0[lo:hi].sum()
        o = emp[lo:hi].sum()
        chi2 += R * (o - e) ** 2 / e
    check(f"B1. {R} simulated switching queues at N = 200 match the exact law (chi-square on 11 df below 31.26)",
          chi2 < 31.26, f"chi2 = {chi2:.1f}")
    for N in NS:
        log(f"\n--- N = {N}")
        Pf, _, _ = M.law(N, "fresh")
        Pr, Qp, Qm = M.law(N, "random")
        Tp, Tm = M.Tp, M.Tm
        check(f"B2. mass one at N = {N}", abs(Pf.sum() - 1) < 1e-9 and abs(Pr.sum() - 1) < 1e-9,
              f"{Pf.sum():.12f}, {Pr.sum():.12f}")
        check(f"B3. fresh atoms P_N(N) = T_+(N) and P_N(0) = 0 at N = {N}", abs(Pf[N] / Tp[N] - 1) < 1e-9 and Pf[0] == 0.0)
        thp, thm, BN = M.scales(N)
        h = M.profile(N)
        log(f"   B_N = {BN:.2f} (theta_+ = {thp:.3f}, theta_- = {thm:.3f}), pN = {M.p * N:.1f}")
        log("   x        B_N P_N(k) fresh   random     h(x)")
        for x in (-2.0, -1.0, 0.0, 1.0, 2.0):
            k = int(round(M.p * N + x * BN))
            xx = (k - M.p * N) / BN
            log(f"   {xx:+.3f}   {BN * Pf[k]:.5f}            {BN * Pr[k]:.5f}    {h(xx):.5f}")
        log("   v      ell   P_N/T_+(N) fresh   I_+(v)    random    I_+(v) + ell^-a/mu_-")
        for ell in (0.3, 0.6, 0.9):
            v = M.p + ell * (1 - M.p)
            k = int(np.floor(v * N))
            I = (a * (1 - ell) * ell ** (-a - 1) + ell ** (-a)) / M.mum
            log(f"   {v:.3f}  {ell:.1f}   {Pf[k] / Tp[N]:8.4f}          {I:8.4f}  {Pr[k] / Tp[N]:8.4f}  {I + ell ** (-a) / M.mum:8.4f}")
        log("   eps    P(N-A_N < eps N) fresh / prediction   random / prediction")
        for eps in (0.05, 0.1, 0.2):
            k0 = int(np.ceil((1 - eps) * N))
            le = 1 - eps / (1 - M.p)
            pf = Pf[k0:].sum()
            pr = Pr[k0:].sum()
            predf = N * Tp[N] * eps * le ** (-a) / M.mum
            predr = predf + N * Tp[N] * le ** (1 - a) / (M.s * (a - 1))
            log(f"   {eps:.2f}   {pf / predf:.3f}                              {pr / predr:.3f}")
        k1 = int(np.floor(0.1 * N))
        le = 1 - 0.1 / M.p
        log(f"   P(A_N < 0.1 N) fresh / prediction: {Pf[:k1 + 1].sum() / (N * Tm[N] * 0.1 * le ** (-a) / M.mup):.3f}")
        nsf = Pf[N] + Pf[0]
        nsr = Pr[N] + Pr[0]
        pred_ratio = N * (Tp[N] + Tm[N]) / (M.s * (a - 1)) / Tp[N]
        log(f"   no switch: fresh {nsf:.4e}, random {nsr:.4e}; ratio {nsr / nsf:.1f}, asymptotic {pred_ratio:.1f}")
        nm = local_maxima(Pf)
        um = np.zeros(60)
        um[0] = 1.0
        for j in range(1, 60):
            um[j] = np.dot(M.fm[1:j + 1], um[j - 1::-1][:j])
        check(f"B4. the fresh law has exactly 3 modes at N = {N}", nm == 3, f"{nm} local maxima")
        check(f"B5. u_- strictly decreasing on 1 <= j < 60", bool(np.all(np.diff(um[1:]) < 0)))
    log("\n--- global mode (Corollary cor:exposure-mode(b)): larger endpoint atom over the largest interior value")
    for alpha in (1.5, 1.8):
        Mg = M if alpha == 1.5 else Model(alpha, 0.6, 0.4, max(NS) + 2)
        expect = "endpoint" if alpha < PHI else "interior"
        for N in NS:
            for start in ("random", "ctrl"):
                P, _, _ = Mg.law(N, start)
                r = max(P[0], P[N]) / P[1:N].max()
                where = "endpoint" if r > 1 else "interior"
                check(f"B6. alpha = {alpha}, N = {N}, {start:6s} start: {where} (predicted {expect})", where == expect,
                      f"ratio {r:.3f}")


def main():
    t0 = time.time()
    rng = np.random.default_rng(20261027)
    part_a(rng)
    part_b(rng)
    sha = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    log(f"\n{'PASS' if not FAILS else 'FAIL'}  verify_exposure ({len(FAILS)} failures, {time.time() - t0:.1f} s)")
    header = ["# script: verify_exposure.py", f"# sha256: {sha}", f"# date: {date.today().isoformat()}",
              f"# python {platform.python_version()}, numpy {np.__version__}", ""]
    (HERE / "data" / "verify_exposure_output.txt").write_text("\n".join(header + LINES) + "\n", encoding="utf-8")
    sys.exit(0 if not FAILS else 1)


if __name__ == "__main__":
    main()
