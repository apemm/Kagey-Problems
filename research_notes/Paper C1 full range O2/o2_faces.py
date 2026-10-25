# o2_faces.py -- P5 and P6.
#  P5: three-state chain, proper face F = {1,2} with exit rates. Exact face maximum
#      M_F at N = 4000 against the new prediction N^-1 T^(1/2) K_F^(h) (1 - h lambda_F)^N
#      and the old one N^-1 T^(1/2) K_F e^(-T lambda_F); location of the maximizer.
#  P6: the same chain on its full face (non-reversible, k = 3), N = 600: the local law
#      ratio R at interior points with the discrete exponent and constant.
# Run with: py -I o2_faces.py
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from o2_lib import (dp_two_state_log, dp_three_state_log, rate,  # noqa: E402
                    constant_hessian_route, constant_torus_route, perron_lr)

A3 = np.array([[0, 2, 0.7], [0.5, 0, 1], [1.5, 0.3, 0]])
q3 = A3.sum(axis=1)  # conservative on the three states: 2.7, 1.5, 1.8
mu3 = np.array([0.5, 0.3, 0.2])
print("rates A =", A3.tolist(), " q =", q3.tolist(), " mu =", mu3.tolist())
print("cycle products q12 q23 q31 =", A3[0, 1] * A3[1, 2] * A3[2, 0],
      " q13 q32 q21 =", A3[0, 2] * A3[2, 1] * A3[1, 0], "(non-reversible)")

# ---------------------------------------------------------------- P5
AF = A3[:2, :2]
qF = q3[:2]
muF = mu3[:2]
QF = AF - np.diag(qF)
w, V = np.linalg.eig(QF)
lam = -max(w.real)
r0, l0 = perron_lr(qF - lam, AF)
astar = l0 * r0
KF = constant_hessian_route(astar, 0.0, AF, qF, muF)
print(f"\nP5: face {{1,2}}: lambda_F = {lam:.6f}, alpha*_F = {astar.round(6).tolist()}, K_F = {KF:.6f}")
N = 4000
print("    T    h     M_F/new    T(M_F/new-1)  M_F/old    exp(-T^2 lam^2/2N)   T|alpha_hat-alpha*|"
      "  min J_h vs -log(1-h lam)/h")
for T in (16, 40, 63, 100, 200, 400, 1000):
    h = T / N
    L = dp_two_state_log(N, h, AF, qF, muF)
    inner = L[1:N]
    i = int(np.argmax(inner)) + 1
    logM = L[i]
    KFh = constant_hessian_route(astar, h, AF, qF, muF)
    new = -math.log(N) + 0.5 * math.log(T) + math.log(KFh) + N * math.log(1 - h * lam)
    old = -math.log(N) + 0.5 * math.log(T) + math.log(KF) - T * lam
    Jmin = rate(astar, h, AF, qF)[0]
    # also: is alpha* the minimizer of J_h? compare with neighbours
    Jl = rate(astar + np.array([1e-3, -1e-3]), h, AF, qF)[0]
    Jr = rate(astar - np.array([1e-3, -1e-3]), h, AF, qF)[0]
    ok = Jl > Jmin and Jr > Jmin
    print(f"{T:6d} {h:.4f}  {math.exp(logM - new):.5f}   {T * (math.exp(logM - new) - 1):+8.4f}"
          f"     {math.exp(logM - old):.5f}     {math.exp(-T * T * lam * lam / (2 * N)):.5f}"
          f"            {T * abs(i / N - astar[0]):7.3f}          "
          f"{Jmin:.10f} {-math.log(1 - h * lam) / h:.10f} min:{ok}")
print("    K_F^(h)/K_F at h = 0.1:", constant_hessian_route(astar, 0.1, AF, qF, muF) / KF,
      " 1/(1 - h lambda_F) =", 1 / (1 - 0.1 * lam))

# ---------------------------------------------------------------- P6
N = 600
Qfull = A3 - np.diag(q3)
w, V = np.linalg.eig(Qfull.T)
pi = np.abs(V[:, np.argmax(w.real)].real)
pi /= pi.sum()
print(f"\nP6: full face, N = {N}, stationary law {pi.round(4).tolist()}")
pts = [pi, np.array([0.3, 0.3, 0.4]), np.array([0.25, 0.45, 0.30]), np.array([0.2, 0.6, 0.2])]
print("   T    h    alpha                C(hess)/C(torus)-1   R (discrete)   T(R-1)   R (continuum)")
for T in (20, 40, 60):
    h = T / N
    L = dp_three_state_log(N, h, A3, q3, mu3)
    for a in pts:
        n = np.round(a * N).astype(int)
        n[2] = N - n[0] - n[1]
        al = n / N
        Ch = constant_hessian_route(al, h, A3, q3, mu3)
        Ct, grad, _ = constant_torus_route(al, h, A3, q3, mu3)
        Jh = rate(al, h, A3, q3)[0]
        C0 = constant_hessian_route(al, 0.0, A3, q3, mu3)
        J0 = rate(al, 0.0, A3, q3)[0]
        lp = L[n[0], n[1]]
        R = math.exp(lp - (-2 * math.log(N) + math.log(T) + math.log(Ch) - T * Jh))
        Rc = math.exp(lp - (-2 * math.log(N) + math.log(T) + math.log(C0) - T * J0))
        print(f"{T:4d} {h:.4f} {str(al.round(3).tolist()):22s} {Ch / Ct - 1:+.1e}"
              f"           {R:.5f}     {T * (R - 1):+.3f}    {Rc:.5f}")
