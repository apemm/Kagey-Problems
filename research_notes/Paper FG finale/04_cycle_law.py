"""Regeneration cycles of a slotted Geo/G/1 queue: exact mass function and its local asymptotics.

Model. Time is slotted. In each slot a customer arrives with probability lam (at most one per slot)
and brings sigma slots of work, sigma i.i.d. with the zeta law P(sigma = n) = n^(-alpha-1)/zeta(alpha+1),
n >= 1. So the work W_t that arrives in slot t has P(W = 0) = 1 - lam and P(W = n) = lam P(sigma = n)
for n >= 1, with mean rho = lam zeta(alpha)/zeta(alpha+1) < 1. The server does one unit of work per
slot: V_t = max(V_{t-1} - 1, 0) + W_t. A regeneration is an epoch with V_t = 0, and the cycle C is the
number of slots between consecutive regenerations (an idle slot is a cycle of length 1).

Facts checked here.
  1. Cyclic lemma: P(C = n) = P(U_n = n - 1)/n, U_n = W_1 + ... + W_n. Checked against a dynamic
     program on the workload (the queue itself) for n <= 300, and the FFT computation of U_n against
     direct convolution for n <= 1000.
  2. Mass and mean: sum_n P(C = n) -> 1 and E C = 1/(1 - rho) (tail of the mean by the asymptotic).
  3. Local asymptotics (Lemma 1 of 04_exposure_queues.md):
        P(C = n) ~ f_W((1 - rho) n) ~ lam (1 - rho)^(-alpha-1) n^(-alpha-1)/zeta(alpha+1).
     Printed as ratios up to n = 2^14.
  4. (LD) and (LD2): n Delta f_C(n)/f_C(n) -> -(alpha+1) and n^2 Delta^2 f_C(n)/f_C(n) -> (alpha+1)(alpha+2),
     printed; and strict log-convexity of f_C on the computed range (a finite check, not a proof).
  5. Monte Carlo of the queue (cycle lengths) against the exact mass function.

Run:  py -I 04_cycle_law.py      Output: 04_cycle_law_output.txt next to this script.
"""
import sys
import time
from pathlib import Path

import numpy as np
from scipy.special import zeta

HERE = Path(__file__).resolve().parent
LINES = []
FAILS = []


def log(msg=""):
    print(msg, flush=True)
    LINES.append(msg)


def check(name, cond, detail=""):
    log(f"{'PASS' if cond else 'FAIL'}  {name}" + (f"  ({detail})" if detail else ""))
    if not cond:
        FAILS.append(name)


def work_pmf(alpha, lam, M):
    """f_W(0..M) for Bernoulli(lam) arrivals and zeta(alpha+1) service."""
    n = np.arange(1, M + 1, dtype=float)
    fW = np.zeros(M + 1)
    fW[0] = 1.0 - lam
    fW[1:] = lam * n ** (-alpha - 1.0) / zeta(alpha + 1.0)
    return fW


def rho_of(alpha, lam):
    return lam * zeta(alpha) / zeta(alpha + 1.0)


def lam_of(alpha, rho):
    return rho * zeta(alpha + 1.0) / zeta(alpha)


def cycle_pmf(alpha, lam, nmax):
    """f_C(1..nmax) (index 0 unused) by the cyclic lemma, with U_n computed by repeated FFT
    convolution truncated to [0, nmax]. Truncation is exact for the values used: U_n = n - 1 <= nmax."""
    M = nmax
    fW = work_pmf(alpha, lam, M)
    size = 1
    while size < 2 * (M + 1):
        size *= 2
    FW = np.fft.rfft(fW, size)
    u = np.zeros(M + 1)
    u[0] = 1.0
    fC = np.zeros(nmax + 1)
    for n in range(1, nmax + 1):
        u = np.fft.irfft(np.fft.rfft(u, size) * FW, size)[:M + 1]
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
    """P(C = n) from the workload recursion itself: start empty, V_1 = W_1, then V = V - 1 + W while
    V >= 1; the cycle ends at the first slot with V = 0. Workloads above the remaining horizon cannot
    return to 0 in time and are dropped."""
    fW = work_pmf(alpha, lam, nmax + 1)
    fC = np.zeros(nmax + 1)
    fC[1] = fW[0]
    dist = fW[1:nmax + 1].copy()          # dist[v-1] = P(V_1 = v, cycle not over), v = 1..nmax
    for n in range(2, nmax + 1):
        # V_n = V_{n-1} - 1 + W_n
        new = np.convolve(dist, fW)[:nmax + 1]   # new[i] = P(V_{n-1} - 1 + W_n = i)
        fC[n] = new[0]
        dist = new[1:nmax + 1]
        dist[max(0, nmax - n):] = 0.0
    return fC


def main():
    t0 = time.time()
    rng = np.random.default_rng(20261026)
    for alpha, rho in ((1.5, 0.4), (1.5, 0.6), (1.8, 0.5)):
        lam = lam_of(alpha, rho)
        log(f"=== alpha = {alpha}, rho = {rho}, lam = {lam:.6f}")
        # 1. cyclic lemma against the queue dynamics, FFT against direct convolution
        n1 = 300
        dp = cycle_pmf_queue_dp(alpha, lam, n1)
        fC_small = cycle_pmf_direct(alpha, lam, 1000)
        rel = np.max(np.abs(dp[1:] - fC_small[1:n1 + 1]) / fC_small[1:n1 + 1])
        check("cyclic lemma vs workload dynamic program, n <= 300", rel < 1e-10, f"max rel diff {rel:.2e}")
        nmax = 2 ** 14
        fC = cycle_pmf(alpha, lam, nmax)
        rel = np.max(np.abs(fC[1:1001] - fC_small[1:]) / fC_small[1:])
        check("FFT vs direct convolution, n <= 1000", rel < 1e-8, f"max rel diff {rel:.2e}")
        # 2. mass and mean, with the tail beyond nmax from the asymptotic
        cst = lam * (1 - rho) ** (-alpha - 1) / zeta(alpha + 1)      # f_C(n) ~ cst n^(-alpha-1)
        n = np.arange(nmax + 1, dtype=float)
        tail_mass = cst * nmax ** (-alpha) / alpha
        tail_mean = cst * nmax ** (1 - alpha) / (alpha - 1)
        mass = fC[1:].sum() + tail_mass
        mean = (n[1:] * fC[1:]).sum() + tail_mean
        check("total mass 1 (with asymptotic tail)", abs(mass - 1) < 1e-6, f"{mass:.10f}")
        check("mean 1/(1-rho) (with asymptotic tail)", abs(mean * (1 - rho) - 1) < 1e-3,
              f"E C = {mean:.6f}, 1/(1-rho) = {1/(1-rho):.6f}")
        # 3. local asymptotics
        fW = work_pmf(alpha, lam, nmax)
        log("   n      f_C(n)        f_C/[cst n^-a-1]   f_C/f_W((1-rho)n)")
        for k in (2 ** e for e in range(4, 15)):
            m = int(round((1 - rho) * k))
            log(f"{k:6d}  {fC[k]:.6e}   {fC[k] / (cst * k ** (-alpha - 1)):.6f}           "
                f"{fC[k] / fW[m]:.6f}")
        r_last = fC[nmax] / (cst * nmax ** (-alpha - 1))
        check("ratio to the constant is within 10% at n = 2^14", abs(r_last - 1) < 0.10, f"{r_last:.4f}")
        # 4. (LD), (LD2), log-convexity
        log("   n      n*Df/f    -(a+1)    n^2*D2f/f   (a+1)(a+2)")
        for k in (2 ** e for e in range(5, 14)):
            d1 = k * (fC[k + 1] - fC[k]) / fC[k]
            d2 = k * k * (fC[k + 1] - 2 * fC[k] + fC[k - 1]) / fC[k]
            log(f"{k:6d}  {d1:8.4f}  {-(alpha + 1):8.4f}  {d2:9.4f}   {(alpha + 1) * (alpha + 2):8.4f}")
        lc = fC[2:nmax] ** 2 - fC[1:nmax - 1] * fC[3:nmax + 1]
        check("f_C strictly log-convex on 2 <= n < 2^14", bool(np.all(lc < 0)),
              f"max of f(n)^2 - f(n-1)f(n+1) relative: {np.max(lc / fC[2:nmax] ** 2):.3e}")
        # 5. Monte Carlo of the queue: cycle lengths
        R = 400000
        lengths = np.zeros(R, dtype=np.int64)
        V = np.zeros(R, dtype=np.int64)
        alive = np.ones(R, dtype=bool)
        t = 0
        tmax = 2000
        while alive.any() and t < tmax:
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
        log(f"   Monte Carlo: {R} cycles, {R - lengths.size} longer than {tmax} slots")
        worst = 0.0
        for k in (1, 2, 3, 5, 10, 20, 50):
            emp = np.mean(lengths == k) * lengths.size / R
            se = np.sqrt(fC[k] * (1 - fC[k]) / R)
            z = (emp - fC[k]) / se
            worst = max(worst, abs(z))
            log(f"   P(C={k:3d}): exact {fC[k]:.6f}  empirical {emp:.6f}  z = {z:+.2f}")
        emp_tail = np.mean(lengths > 100) * lengths.size / R + (R - lengths.size) / R
        ex_tail = 1 - fC[1:101].sum()
        log(f"   P(C>100): exact {ex_tail:.6f}  empirical {emp_tail:.6f}")
        check("Monte Carlo agrees with the exact law (|z| < 4.5 at 7 points)", worst < 4.5, f"max |z| {worst:.2f}")
    log(f"time {time.time() - t0:.1f} s; {'all checks passed' if not FAILS else 'FAILED: ' + ', '.join(FAILS)}")
    (HERE / "04_cycle_law_output.txt").write_text("\n".join(LINES) + "\n", encoding="utf-8", newline="\n")
    sys.exit(1 if FAILS else 0)


if __name__ == "__main__":
    main()
