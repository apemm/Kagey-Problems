# o2_table.py -- P2, P3, P4 for the two-state chain q12 = 1, q21 = 2, N = 4000.
#  P2: spread over alpha = n_1/N in [0.45, 0.85] (all lattice points, and the plan's
#      9-point grid) of log P_N(n) + exponent, for the
#      continuum exponent T J_V and the discrete exponent N I_h = T J_h;
#  P3: the ratio R = P_N(n) / (N^-1 T^(1/2) C^(h)(alpha) e^(-N I_h)) and T (R - 1);
#  P4: N I_h - T J_V against (T^2/(2N)) sum_i alpha_i (q_i - theta_i)^2.
# Run with: py -I o2_table.py
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from o2_lib import dp_two_state_log, rate, constant_hessian_route  # noqa: E402

A = [[0, 1], [2, 0]]
q = np.array([1.0, 2.0])
N = 4000
lo, hi = int(math.ceil(0.45 * N)), int(math.floor(0.85 * N))
grid = range(lo, hi + 1)
sub = range(lo, hi + 1, 40)

for mu_name, mu in (("uniform", [0.5, 0.5]), ("stationary", [2 / 3, 1 / 3])):
    print(f"=== start {mu_name} mu = {mu}")
    print(" T     T^2/N   spread(T J_V)  spread(N I_h)  spread(log C_F)  spread(log C^(h))"
          "  max T|R-1|  max T|R_cont-1|")
    for T in (16, 63, 200, 400, 1000):
        h = T / N
        L = dp_two_state_log(N, h, A, q, mu)
        sJ, sI = [], []
        for n1 in grid:
            a = np.array([n1 / N, 1 - n1 / N])
            J0 = rate(a, 0.0, A, q)[0]
            Jh = rate(a, h, A, q)[0]
            sJ.append(L[n1] + T * J0)
            sI.append(L[n1] + T * Jh)
        cF, cH, dev, devc = [], [], [], []
        for n1 in sub:
            a = np.array([n1 / N, 1 - n1 / N])
            C0 = constant_hessian_route(a, 0.0, A, q, mu)
            Ch = constant_hessian_route(a, h, A, q, mu)
            cF.append(math.log(C0))
            cH.append(math.log(Ch))
            Jh = rate(a, h, A, q)[0]
            J0 = rate(a, 0.0, A, q)[0]
            R = math.exp(L[n1] - (-math.log(N) + 0.5 * math.log(T) + math.log(Ch) - T * Jh))
            Rc = math.exp(L[n1] - (-math.log(N) + 0.5 * math.log(T) + math.log(C0) - T * J0))
            dev.append(T * (R - 1))
            devc.append(T * (Rc - 1))
        sp = lambda v: max(v) - min(v)  # noqa: E731
        # the 9-point grid alpha = 0.45, 0.50, ..., 0.85 used in the plan's table
        g9 = [int(round(x * N)) - lo for x in np.linspace(0.45, 0.85, 9)]
        s9J, s9I = sp([sJ[i] for i in g9]), sp([sI[i] for i in g9])
        print(f"      9-point grid: spread(T J_V) {s9J:.3f}  spread(N I_h) {s9I:.3f}")
        print(f"{T:5d} {T * T / N:7.2f}   {sp(sJ):10.3f}    {sp(sI):10.3f}    {sp(cF):10.3f}"
              f"      {sp(cH):10.3f}      {max(abs(x) for x in dev):8.3f}   "
              f"{max(abs(x) for x in devc):10.3g}")

print()
print("P3 detail (uniform start): T (R - 1) at alpha = 0.45, 0.55, 2/3, 0.75, 0.85")
mu = [0.5, 0.5]
pts = [0.45, 0.55, 2 / 3, 0.75, 0.85]
for T in (16, 63, 200, 400, 1000):
    h = T / N
    L = dp_two_state_log(N, h, A, q, mu)
    row = []
    for a1 in pts:
        n1 = int(round(a1 * N))
        a = np.array([n1 / N, 1 - n1 / N])
        Ch = constant_hessian_route(a, h, A, q, mu)
        Jh = rate(a, h, A, q)[0]
        R = math.exp(L[n1] - (-math.log(N) + 0.5 * math.log(T) + math.log(Ch) - T * Jh))
        row.append(T * (R - 1))
    print(f"  T={T:5d}: " + "  ".join(f"{x:+.4f}" for x in row))

print()
print("P4: (N I_h - T J_V) / [(T^2/2N) sum alpha_i (q_i - theta_i)^2]  at alpha = 0.45, 0.55, 0.85 (the term vanishes at 2/3)")
for T in (16, 63, 200, 400, 1000):
    h = T / N
    row = []
    for a1 in (0.45, 0.55, 0.85):
        a = np.array([a1, 1 - a1])
        J0, th0, _ = rate(a, 0.0, A, q)
        Jh = rate(a, h, A, q)[0]
        pred = (T * T / (2 * N)) * float(a @ (q - th0) ** 2)
        row.append((T * Jh - T * J0) / pred)
    print(f"  T={T:5d} h={h:.4f}: " + "  ".join(f"{x:.4f}" for x in row))
