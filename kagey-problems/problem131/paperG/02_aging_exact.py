"""The occupation count of an aged alternating renewal process: exact law and the local aging law.

Model. Runs alternate in sign, the first run (at time 0) is a fresh plus run, run lengths are i.i.d.
with mass function f_+ (plus) and f_- (minus) on {1, 2, ...}. The observation window is the steps
t_a+1, ..., t_a+N, and A_N is the number of plus steps in it. P_N(k) = P(A_N = k).

Exact method (no simulation). Condition on the run that straddles step t_a+1 (the initial run of the
window). Its sign and residual length d have the law
    nu_+(d) = sum_{s=0}^{t_a} u_c(s) f_+(t_a - s + d),   nu_-(d) = sum_{s=0}^{t_a} v_-(s) f_-(t_a - s + d),
where u_c is the renewal mass function of the cycle law f_+ * f_- (plus runs start at the epochs of
u_c) and v_- = f_+ * u_c (minus runs start there). After the initial run the walk is fresh, so
(first-run decomposition, Paper F Prop. first-run)
    P_N(k) = Q_+ 1{k=N} + Q_- 1{k=0} + sum_d nu_+(d) G^-(k-d, N-k) + sum_d nu_-(d) G^+(k, N-k-d),
with G^s(a, b) = P(a fresh walk of sign s has a plus and b minus steps among its first a+b steps),
computed from the fresh identities with the convolution powers u^s_m = f_s^{*m} and the covering
kernels q^s_m (Paper F Prop. fresh-identity). Checked against brute force over all run sequences.

Run:  py -I 02_aging_exact.py        Output: 02_aging_output.txt next to this script.
"""
import math
import sys
import time
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.special import zeta

HERE = Path(__file__).resolve().parent
LINES = []
FAILS = []


def log(msg=""):
    print(msg, flush=True)
    LINES.append(msg)


def check(name, ok, detail=""):
    tag = "PASS" if ok else "FAIL"
    if not ok:
        FAILS.append(name)
    log(f"{tag}  {name}  {detail}")


# ----------------------------------------------------------------------------------------------
# Laws
# ----------------------------------------------------------------------------------------------

def zeta_law(alpha, L, shift=0):
    """f(n) proportional to (n+shift)^(-alpha-1), n = 1..L; T(n) = P(X >= n), n = 0..L+1 (exact tails)."""
    c = zeta(alpha + 1, 1 + shift)
    n = np.arange(L + 2, dtype=float)
    f = np.zeros(L + 2)
    f[1:] = (n[1:] + shift) ** (-alpha - 1) / c
    T = np.ones(L + 2)
    T[1:] = zeta(alpha + 1, n[1:] + shift) / c
    return f, T


def renewal(f, L):
    """u(0..L) with u(0) = 1, u(n) = sum_{i=1}^n f(i) u(n-i)."""
    u = np.zeros(L + 1)
    u[0] = 1.0
    fr = f[1:L + 1][::-1].copy()  # fr[L-1-i] = f(i+1)
    for n in range(1, L + 1):
        # sum_{i=1}^n f(i) u(n-i) = dot(f[1..n], u[n-1..0])
        u[n] = np.dot(f[1:n + 1], u[n - 1::-1])
    return u


def conv_trunc(a, b, L):
    n = 1
    while n < 2 * (L + 1):
        n *= 2
    return np.fft.irfft(np.fft.rfft(a[:L + 1], n) * np.fft.rfft(b[:L + 1], n), n)[:L + 1]


def powers_and_kernels(f, T, N, tol=1e-19):
    """U[m, x] = f^{*m}(x), m = 0..M; Q[m, x] = q_m(x) (m = 1..M+1, row 0 unused), x = 0..N."""
    nfft = 1
    while nfft < 2 * (N + 1):
        nfft *= 2
    Ff = np.fft.rfft(f[:N + 1], nfft)
    Tpos = T[:N + 1].copy()
    Tpos[0] = 0.0
    FT = np.fft.rfft(Tpos, nfft)
    rows = [np.zeros(N + 1)]
    rows[0][0] = 1.0
    while True:
        prev = rows[-1]
        nxt = np.fft.irfft(np.fft.rfft(prev, nfft) * Ff, nfft)[:N + 1]
        nxt[nxt < 0] = 0.0
        m = len(rows)
        nxt[:m] = 0.0  # S_m >= m
        rows.append(nxt)
        if nxt.max() < tol or m >= N:
            break
    U = np.array(rows)  # rows 0..M
    M = U.shape[0] - 1
    Q = np.zeros((M + 2, N + 1))
    for m in range(1, M + 2):
        q = np.fft.irfft(np.fft.rfft(U[m - 1], nfft) * FT, nfft)[:N + 1]
        q[0] = 0.0
        q[q < 0] = 0.0
        Q[m] = q
    return U, Q


class Fresh:
    """Fresh-walk arrays G^-(a, b) and G^+(a, b) for a + b <= N (full matrices)."""

    def __init__(self, fp, Tp, fm, Tm, N):
        self.N = N
        Up, Qp = powers_and_kernels(fp, Tp, N)
        Um, Qm = powers_and_kernels(fm, Tm, N)
        M = max(Up.shape[0], Um.shape[0]) + 1

        def pad(A, rows):
            B = np.zeros((rows, N + 1))
            B[:A.shape[0]] = A
            return B

        Up, Um = pad(Up, M + 1), pad(Um, M + 1)
        Qp, Qm = pad(Qp, M + 2), pad(Qm, M + 2)
        # G^-[a, b] = sum_{m>=1} Up[m,a] Qm[m+1,b] + sum_{m>=1} Qp[m,a] Um[m,b]   (a, b >= 1)
        Gm = Up[1:M + 1].T @ Qm[2:M + 2] + Qp[1:M + 1].T @ Um[1:M + 1]
        # G^+[a, b] = sum_{m>=1} Qp[m+1,a] Um[m,b] + sum_{m>=1} Up[m,a] Qm[m,b]
        Gp = Qp[2:M + 2].T @ Um[1:M + 1] + Up[1:M + 1].T @ Qm[1:M + 1]
        Gm[0, :] = Tm[:N + 1]
        Gm[:, 0] = 0.0
        Gm[0, 0] = 1.0
        Gp[:, 0] = Tp[:N + 1]
        Gp[0, :] = 0.0
        Gp[0, 0] = 1.0
        self.Gm, self.Gp = Gm, Gp


def initial_run_law(fp, Tp, fm, Tm, ta, N):
    """nu_+(d), nu_-(d) for d = 1..N-1 (index d), atoms Q_+ = P(+, D >= N), Q_- likewise."""
    L = ta + N + 2
    fc = conv_trunc(fp, fm, ta)
    uc = renewal(fc, ta)
    vm = conv_trunc(fp, uc, ta)
    s = np.arange(ta + 1)
    nup = np.zeros(N)
    num = np.zeros(N)
    for d in range(1, N):
        idx = ta - s + d
        nup[d] = np.dot(uc, fp[idx])
        num[d] = np.dot(vm, fm[idx])
    Qp = np.dot(uc, Tp[ta - s + N])
    Qm = np.dot(vm, Tm[ta - s + N])
    pip = np.dot(uc, Tp[ta - s + 1])
    pim = np.dot(vm, Tm[ta - s + 1])
    return nup, num, Qp, Qm, pip, pim


def aged_law(fresh, nup, num, Qp, Qm, N):
    P = np.zeros(N + 1)
    Gm, Gp = fresh.Gm, fresh.Gp
    for k in range(N + 1):
        j = N - k
        tot = 0.0
        dmax = min(k, N - 1)
        if dmax >= 1:
            d = np.arange(1, dmax + 1)
            tot += np.dot(nup[d], Gm[k - d, j])
        dmax = min(j, N - 1)
        if dmax >= 1:
            d = np.arange(1, dmax + 1)
            tot += np.dot(num[d], Gp[k, j - d])
        P[k] = tot
    P[N] += Qp
    P[0] += Qm
    return P


# ----------------------------------------------------------------------------------------------
# Brute force
# ----------------------------------------------------------------------------------------------

def brute(fp, Tp, fm, Tm, ta, N):
    M = ta + N
    P = np.zeros(N + 1)

    def rec(pos, sign, prob, plus_in_window):
        # a run of `sign` starts at step pos+1
        f, T = (fp, Tp) if sign > 0 else (fm, Tm)
        rem = M - pos
        for ell in range(1, rem):
            lo, hi = max(pos + 1, ta + 1), min(pos + ell, M)
            add = max(0, hi - lo + 1) if sign > 0 else 0
            rec(pos + ell, -sign, prob * f[ell], plus_in_window + add)
        # last run: length >= rem
        lo, hi = max(pos + 1, ta + 1), M
        add = max(0, hi - lo + 1) if sign > 0 else 0
        P[plus_in_window + add] += prob * T[rem]

    rec(0, 1, 1.0, 0)
    return P


# ----------------------------------------------------------------------------------------------
# Limits
# ----------------------------------------------------------------------------------------------

def lamperti(x, a, b=1.0):
    c = math.cos(math.pi * a)
    return (math.sin(math.pi * a) / math.pi) * b * x ** (a - 1) * (1 - x) ** (a - 1) / (
        b * b * x ** (2 * a) + 2 * b * c * x ** a * (1 - x) ** a + (1 - x) ** (2 * a))


def rho_DL(z, a, theta, share):
    return share * (math.sin(math.pi * a) / math.pi) * theta ** a * z ** (-a) / (theta + z)


def lam_pair(w, w1, a, b=1.0):
    """Lamperti density at w, with w1 = 1 - w passed separately (mpmath numbers)."""
    if w <= 0 or w1 <= 0:
        return mp.mpf(0)
    c = mp.cos(mp.pi * a)
    return (mp.sin(mp.pi * a) / mp.pi) * b * w ** (a - 1) * w1 ** (a - 1) / (
        b * b * w ** (2 * a) + 2 * b * c * w ** a * w1 ** a + w1 ** (2 * a))


def L_aged(x, a, theta, b=1.0):
    sp, sm = 1.0 / (1.0 + b), b / (1.0 + b)
    mp.mp.dps = 18
    x = mp.mpf(x)
    K = mp.sin(mp.pi * a) / mp.pi * mp.mpf(theta) ** a
    f1 = lambda z: sp * K * z ** (-a) / (theta + z) * lam_pair((x - z) / (1 - z), (1 - x) / (1 - z), a, b) / (1 - z)
    f2 = lambda z: sm * K * z ** (-a) / (theta + z) * lam_pair(x / (1 - z), (1 - z - x) / (1 - z), a, b) / (1 - z)
    return float(mp.quad(f1, [0, x / 2, x])) + float(mp.quad(f2, [0, (1 - x) / 2, 1 - x]))


def atom_aged(a, theta, share):
    return share * (math.sin(math.pi * a) / math.pi) * float(mp.betainc(a, 1 - a, 0, theta / (1 + theta)))


def layer_const(a, theta, share):
    g = lambda z: rho_DL(float(z), a, theta, share) * float(1 - z) ** (-a)
    return float(mp.quad(g, [0, 0.5, 1]))


# ----------------------------------------------------------------------------------------------

def main():
    t0 = time.time()

    log("=== P9: brute force (all run sequences), fresh plus start at time 0")
    for a in (0.5, 1.5):
        fp, Tp = zeta_law(a, 40)
        fm, Tm = zeta_law(a, 40, shift=2)
        for ta, N in ((0, 12), (5, 9), (9, 5), (3, 11)):
            fr = Fresh(fp, Tp, fm, Tm, N)
            nup, num, Qp, Qm, _, _ = initial_run_law(fp, Tp, fm, Tm, ta, N)
            P = aged_law(fr, nup, num, Qp, Qm, N)
            B = brute(fp, Tp, fm, Tm, ta, N)
            err = np.abs(P - B).max()
            check(f"alpha={a} ta={ta} N={N} exact vs brute", err < 1e-14, f"(max diff {err:.2e}, mass {P.sum():.15f})")

    log("")
    log("=== Dynkin-Lamperti identity: int_0^t (t-A)^(a-1)(A+R)^(-a-1) dA = t^a/(a R^a (t+R))")
    for a in (0.3, 0.7):
        for (t, R) in ((1.0, 0.5), (2.0, 3.0)):
            mp.mp.dps = 30
            lhs = mp.quad(lambda A: (t - A) ** (a - 1) * (A + R) ** (-a - 1), [0, t])
            rhs = t ** a / (a * R ** a * (t + R))
            check(f"DL identity a={a} t={t} R={R}", abs(lhs / rhs - 1) < 1e-9, f"(ratio {float(lhs / rhs):.15f})")

    # ------------------------------------------------------------------------------------------
    log("")
    log("=== Infinite mean (0 < alpha < 1), symmetric zeta laws, b = 1")
    xs = [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9]
    for a in (0.5, 0.7):
        for theta in (0.5, 1.0, 2.0):
            Lth = [L_aged(x, a, theta) for x in xs]
            Qinf = atom_aged(a, theta, 0.5)
            cplus = layer_const(a, theta, 0.5)
            mp.mp.dps = 20
            massL = float(mp.quad(lambda x: L_aged(x, a, theta), [0, 0.25, 0.5, 0.75, 1]))
            check(f"P4 mass a={a} theta={theta}", abs(massL + 2 * Qinf - 1) < 1e-6,
                  f"(int L_theta = {massL:.8f}, atoms 2*{Qinf:.8f}, total {massL + 2 * Qinf:.8f})")
            Qcheck = float(mp.quad(lambda z: rho_DL(float(z), a, theta, 0.5), [1, 2, mp.inf]))
            check(f"atom formula a={a} theta={theta}", abs(Qcheck / Qinf - 1) < 1e-8, f"({Qinf:.10f} vs {Qcheck:.10f})")
            log(f"  a={a} theta={theta}: L_theta(x) = " + " ".join(f"{v:.5f}" for v in Lth)
                + f"   fresh L(x) = " + " ".join(f"{lamperti(x, a):.5f}" for x in xs))
            log(f"  atom Q_inf = {Qinf:.6f}, layer constant c_+ = {cplus:.6f}")
            log("     N   max|rel err| on x in [0.1,0.9]   ratios N P_N/L_theta at x=" + ",".join(str(x) for x in xs))
            for N in (500, 1000, 2000):
                ta = round(theta * N)
                fp, Tp = zeta_law(a, ta + N + 5)
                fr = Fresh(fp, Tp, fp, Tp, N)
                nup, num, Qp, Qm, pip, pim = initial_run_law(fp, Tp, fp, Tp, ta, N)
                P = aged_law(fr, nup, num, Qp, Qm, N)
                rat = [N * P[int(math.floor(x * N))] / L for x, L in zip(xs, Lth)]
                mx = max(abs(r - 1) for r in rat)
                log(f"  {N:5d}   {mx:.4f}                          " + " ".join(f"{r:.4f}" for r in rat))
                u = renewal(fp, 6)
                lay = [P[N - j] / (Tp[N] * u[j]) for j in range(1, 6)]
                log(f"         mass {P.sum():.12f}; atom P_N(N) = {P[N]:.6f} (ratio to Q_inf {P[N] / Qinf:.4f});"
                    f" pi_+ = {pip:.4f}")
                log(f"         layer P_N(N-j)/(T(N)u(j)), j=1..5: " + " ".join(f"{v:.4f}" for v in lay)
                    + f"  (ratio to c_+: {lay[0] / cplus:.4f} .. {lay[-1] / cplus:.4f})")
                zs = [0.2, 0.5, 0.8]
                log("         N nu_+(zN)/rho_+(z), z=0.2,0.5,0.8: "
                    + " ".join(f"{N * nup[int(z * N)] / rho_DL(z, a, theta, 0.5):.4f}" for z in zs))
                if N == 2000 and a == 0.5:
                    if theta == 1.0:
                        check("P1 a=0.5 theta=1 N=2000 max rel err < 5%", mx < 0.05, f"({mx:.4f})")
                    check(f"P2 a=0.5 theta={theta} N=2000 atom within 5%", abs(P[N] / Qinf - 1) < 0.05,
                          f"({P[N] / Qinf:.4f})")
                    check(f"P3 a=0.5 theta={theta} N=2000 layer within 10%",
                          max(abs(v / cplus - 1) for v in lay) < 0.10, f"({min(lay) / cplus:.4f}..{max(lay) / cplus:.4f})")
                if N == 2000 and a == 0.7 and theta == 1.0:
                    check("P1 a=0.7 theta=1 N=2000 max rel err < 15%", mx < 0.15, f"({mx:.4f})")
            log("")

    # ------------------------------------------------------------------------------------------
    log("=== Finite mean (1 < alpha < 2), symmetric zeta, alpha = 1.5")
    a = 1.5
    mu = zeta(a) / zeta(a + 1)
    s = 2 * mu
    p = 0.5
    log(f"  mu = {mu:.6f}, s = {s:.6f}")
    lams = [0.3, 0.5, 0.7]
    for theta in (0.5, 1.0, 2.0):
        for N in (500, 1000, 2000):
            ta = round(theta * N)
            fp, Tp = zeta_law(a, ta + N + 5)
            fr = Fresh(fp, Tp, fp, Tp, N)
            nup, num, Qp, Qm, pip, pim = initial_run_law(fp, Tp, fp, Tp, ta, N)
            P = aged_law(fr, nup, num, Qp, Qm, N)
            n0 = np.zeros(N)
            n0[1:] = fp[1:N]
            F0 = aged_law(fr, n0, np.zeros(N), Tp[N], 0.0, N)  # fresh plus start
            # B_N: T(B_N) = s/N
            BN = float(np.searchsorted(-Tp[:N + 1], -s / N))
            u = renewal(fp, N)
            # bulk: aged vs fresh on |k - N/2| <= B_N
            ks = np.arange(int(N / 2 - BN), int(N / 2 + BN) + 1)
            bulk = np.abs(P[ks] / F0[ks] - 1).max()
            # big-jump zone
            out = []
            for lam in lams:
                k = int(round(p * N + (1 - p) * lam * N))
                Lk = (k - p * N) / (1 - p)
                iL = int(math.floor(Lk))
                j = N - k
                kap = pip * u[j] * (j >= 1) + sum(num[d] * u[j - d] for d in range(1, min(j, N - 1) + 1))
                Gnu = (N - Lk) / mu * fp[iL] + Tp[iL] * kap
                Psi = nup[iL] * (1 + mu * u[j])
                pred = Gnu + Psi
                predF = (N - Lk) / mu * fp[iL] + Tp[iL] * u[j]  # fresh plus kernel (limit coefficient)
                l = Lk / N
                asym = Tp[N] / mu * (a * (1 - l) * l ** (-a - 1) + 2 * l ** (-a) - (l + theta) ** (-a))
                out.append((lam, P[k] / pred, P[k] / asym, Psi / pred, F0[k] / predF))
            atom_rt = Qp / (sum(Tp[np.arange(ta + 1) + N]) / s)
            atom_lim = Qp / (N * Tp[N] * (1 - (1 + theta) ** (1 - a)) / (s * (a - 1)))
            lay = []
            for jj in range(1, 6):
                pr = p * u[jj] + 1 / s + (1 / s) * (1 - (1 + theta) ** (-a)) * (1 + mu * u[jj])
                lay.append(P[N - jj] / Tp[N] / pr)
            log(f"  theta={theta} N={N} B_N={BN:.0f}: mass {P.sum():.12f}; bulk max|aged/fresh-1| = {bulk:.4f}")
            for (lam, r1, r2, fr_, rf) in out:
                log(f"     lambda={lam}: P/Pred = {r1:.4f}, P/asymptotic = {r2:.4f}, aging share of Pred = {fr_:.3f};"
                    f" fresh control P/G = {rf:.4f}")
            log(f"     atom P_N(N)={Qp:.6f}: ratio to (1/s)sum_a T(a+N) = {atom_rt:.4f}, to the limit formula = {atom_lim:.4f}")
            log(f"     layer P_N(N-j)/(T(N) pred(j)), j=1..5: " + " ".join(f"{v:.4f}" for v in lay))
            if N == 2000 and theta == 1.0:
                check("P5 bulk aged vs fresh within 2% (theta=1, N=2000)", bulk < 0.02, f"({bulk:.4f})")
                check("P6 big-jump P/Pred within 10% (theta=1, N=2000)", max(abs(o[1] - 1) for o in out) < 0.10,
                      "(" + ", ".join(f"{o[1]:.4f}" for o in out) + ")")
                check("P7 atom within 10% of limit (theta=1, N=2000)", abs(atom_lim - 1) < 0.10, f"({atom_lim:.4f})")
                check("P8 layer within 10% (theta=1, N=2000)", max(abs(v - 1) for v in lay) < 0.10,
                      "(" + ", ".join(f"{v:.4f}" for v in lay) + ")")
        log("")

    log(f"elapsed {time.time() - t0:.0f} s; failures: {FAILS if FAILS else 'none'}")
    (HERE / "02_aging_output.txt").write_text("\n".join(LINES) + "\n", encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
