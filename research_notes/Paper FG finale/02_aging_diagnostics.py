"""Diagnostics added after the pre-registered run of 02_aging_exact.py (not predictions).

D1. Infinite mean, end layer with the leading correction: the minus initial run of residual d <= j
    contributes T_+(N) sum_{d<=j} nu_-(d) u_-(j-d), which is o(T_+(N)) but only by a factor of order
    1/(N T(N)). Compare P_N(N-j) with T_+(N)[c_+ u_-(j) + sum_{d<=j} nu_-(d) u_-(j-d)].
D2. Finite mean, big-jump zone: the aging increment P_aged(k) - P_fresh(k) against the predicted
    increment T_+(L_k)(kappa^(N)_+(N-k) - u_-(N-k)) + nu^(N)_+(L_k)(1 + mu_+ u_-(N-k)). This removes the
    slow finite-N bias that the fresh kernel of Paper F already has.
D3. Asymmetric laws (b != 1): plus zeta, minus f(n) proportional to (n+3)^(-a-1). Checks the sign share
    1/(1+b) of the straddling run and the mixture density with L_{a,b}.
D4. Closed form of the layer constant: c_+(theta) = s_+ (sin pi a/pi) theta^(a-1) B(1-a,1-a)
    2F1(1, 1-a; 2-2a; -1/theta).

Run:  py -I 02_aging_diagnostics.py      Output: 02_aging_diagnostics_output.txt
"""
import importlib.util
import math
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.special import zeta

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("aging", HERE / "02_aging_exact.py")
E = importlib.util.module_from_spec(spec)
spec.loader.exec_module(E)

LINES = []


def log(msg=""):
    print(msg, flush=True)
    LINES.append(msg)


def main():
    log("=== D4: closed form of c_+(theta)")
    for a in (0.3, 0.5, 0.7):
        for theta in (0.5, 1.0, 2.0):
            num = E.layer_const(a, theta, 0.5)
            cf = 0.5 * math.sin(math.pi * a) / math.pi * theta ** (a - 1) * float(
                mp.beta(1 - a, 1 - a) * mp.hyp2f1(1, 1 - a, 2 - 2 * a, -1 / theta))
            log(f"  a={a} theta={theta}: quadrature {num:.10f}, closed form {cf:.10f}")

    log("")
    log("=== D1: infinite mean, layer with the minus-initial-run correction (alpha = 0.5)")
    a = 0.5
    for theta in (0.5, 1.0):
        cplus = E.layer_const(a, theta, 0.5)
        for N in (500, 1000, 2000):
            ta = round(theta * N)
            fp, Tp = E.zeta_law(a, ta + N + 5)
            fr = E.Fresh(fp, Tp, fp, Tp, N)
            nup, num, Qp, Qm, _, _ = E.initial_run_law(fp, Tp, fp, Tp, ta, N)
            P = E.aged_law(fr, nup, num, Qp, Qm, N)
            u = E.renewal(fp, 6)
            r0, r1 = [], []
            for j in range(1, 6):
                corr = sum(num[d] * u[j - d] for d in range(1, j + 1))
                r0.append(P[N - j] / (Tp[N] * cplus * u[j]))
                r1.append(P[N - j] / (Tp[N] * (cplus * u[j] + corr)))
            log(f"  theta={theta} N={N}: leading ratio " + " ".join(f"{v:.4f}" for v in r0)
                + "   corrected ratio " + " ".join(f"{v:.4f}" for v in r1))

    log("")
    log("=== D2: finite mean (alpha = 1.5), aging increment in the big-jump zone")
    a = 1.5
    mu = zeta(a) / zeta(a + 1)
    p = 0.5
    for theta in (0.5, 1.0, 2.0):
        for N in (500, 1000, 2000):
            ta = round(theta * N)
            fp, Tp = E.zeta_law(a, ta + N + 5)
            fr = E.Fresh(fp, Tp, fp, Tp, N)
            nup, num, Qp, Qm, pip, pim = E.initial_run_law(fp, Tp, fp, Tp, ta, N)
            P = E.aged_law(fr, nup, num, Qp, Qm, N)
            n0 = np.zeros(N)
            n0[1:] = fp[1:N]
            F0 = E.aged_law(fr, n0, np.zeros(N), Tp[N], 0.0, N)
            u = E.renewal(fp, N)
            out = []
            for lam in (0.3, 0.5, 0.7):
                k = int(round(p * N + (1 - p) * lam * N))
                Lk = (k - p * N) / (1 - p)
                iL = int(math.floor(Lk))
                j = N - k
                kap = pip * u[j] + sum(num[d] * u[j - d] for d in range(1, min(j, N - 1) + 1))
                dpred = Tp[iL] * (kap - u[j]) + nup[iL] * (1 + mu * u[j])
                out.append((P[k] - F0[k]) / dpred)
            log(f"  theta={theta} N={N}: increment ratio at lambda=0.3,0.5,0.7: " + " ".join(f"{v:.4f}" for v in out))

    log("")
    log("=== D3: asymmetric laws, alpha = 0.5, theta = 1 (plus zeta, minus shifted by 3)")
    a, theta = 0.5, 1.0
    b = zeta(a + 1) / zeta(a + 1, 4)
    xs = [0.1, 0.3, 0.5, 0.7, 0.9]
    Lth = [E.L_aged(x, a, theta, b) for x in xs]
    sp = 1 / (1 + b)
    Qp_inf = E.atom_aged(a, theta, sp)
    Qm_inf = E.atom_aged(a, theta, 1 - sp)
    log(f"  b = {b:.6f}; L_(theta)(x) = " + " ".join(f"{v:.5f}" for v in Lth)
        + f"; atoms Q+ = {Qp_inf:.5f}, Q- = {Qm_inf:.5f}")
    for N in (500, 1000, 2000):
        ta = round(theta * N)
        fp, Tp = E.zeta_law(a, ta + N + 5)
        fm, Tm = E.zeta_law(a, ta + N + 5, shift=3)
        fr = E.Fresh(fp, Tp, fm, Tm, N)
        nup, num, Qp, Qm, pip, pim = E.initial_run_law(fp, Tp, fm, Tm, ta, N)
        P = E.aged_law(fr, nup, num, Qp, Qm, N)
        rat = [N * P[int(math.floor(x * N))] / L for x, L in zip(xs, Lth)]
        log(f"  N={N}: mass {P.sum():.12f}; ratios " + " ".join(f"{r:.4f}" for r in rat)
            + f"; atoms {Qp / Qp_inf:.4f}, {Qm / Qm_inf:.4f}; P(+ at t_a) = {pip:.4f} (limit {sp:.4f})")

    (HERE / "02_aging_diagnostics_output.txt").write_text("\n".join(LINES) + "\n", encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
