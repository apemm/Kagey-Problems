# check_exact.py -- prediction P1 and the facet functions.
# (1) the transfer-matrix recursion against brute force on small N;
# (2) Lemma layer-exact-discrete against the recursion, for a pair face, the
#     3-cycle (facet with 2 states) and a 4-state face (facet with 3 states);
# (3) the continued J_G(beta,z), C_G(beta,z) against the closed form of
#     Lemma L-two for the 3-cycle, at real and complex z, and the paper's value
#     omega_beta = 2 + (9/4) sqrt 2 (Proposition layer-cubic).
# Paper C1 (problem 131), boundary layer at a facet, item O1.
# Run: py -I check_exact.py
import os, sys, math, cmath
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from dl_lib import (make_chain, brute_law, dp_face, weighted_poly, lemma_rhs,
                    Facet)

PAIR = make_chain({(0, 1): 1.0, (1, 0): 2.0}, [0.6, 0.4])
CYC = make_chain({(0, 1): 2, (1, 2): 2, (2, 0): 2, (1, 0): 1, (2, 1): 1, (0, 2): 1},
                 [0.4, 0.35, 0.25])
R4 = {(0, 1): 2.0, (0, 2): 0.5, (0, 3): 1.0, (1, 0): 0.5, (1, 2): 1.5, (1, 3): 0.7,
      (2, 0): 1.0, (2, 1): 0.4, (2, 3): 1.2, (3, 0): 0.8, (3, 1): 1.6, (3, 2): 0.6}
FOUR = make_chain(R4, [0.3, 0.3, 0.2, 0.2])
CASES = [("pair", PAIR, [0, 1], 1), ("3-cycle", CYC, [0, 1, 2], 2),
         ("4-state", FOUR, [0, 1, 2, 3], 3)]

print("(1) recursion vs brute force, N = 8, h = 0.1")
for name, (Q, mu), F, i in CASES:
    N = 8
    br = brute_law(Q, mu, 0.1, F, N)
    target = [N] * len(F)
    read = {N: list(br.keys())}
    dp = dp_face(Q, mu, 0.1, F, target, read)
    err = max(abs(dp[(N, c)] - v) / v for c, v in br.items() if v > 0)
    print(f"  {name:8s} compositions {len(br):4d}  max rel diff {err:.2e}")

print("(2) Lemma layer-exact-discrete vs recursion")
for name, (Q, mu), F, i in CASES:
    k = len(F)
    Np = {2: 40, 3: 30, 4: 24}[k]
    h = 0.15
    G = [s for s in F if s != i]
    nhat = [Np // (k - 1)] * (k - 1)
    nhat[0] += Np - sum(nhat)
    nimax = 7
    target = [0] * k
    for a, s in enumerate(G):
        target[F.index(s)] = nhat[a]
    target[F.index(i)] = nimax
    read = {}
    for ni in range(0, nimax + 1):
        c = list(target)
        c[F.index(i)] = ni
        read.setdefault(Np + ni, []).append(tuple(c))
    dp = dp_face(Q, mu, h, F, target, read)
    coef = weighted_poly(Q, mu, h, F, i, nhat, nimax)
    c0 = list(target)
    c0[F.index(i)] = 0
    print(f"  {name}: N' = {Np}, n-hat = {nhat}, h = {h}")
    print(f"    K=0 coefficient vs P_N'(n-hat): {coef[0]:.12e} {dp[(Np, tuple(c0))]:.12e}")
    for ni in range(1, nimax + 1):
        c = list(target)
        c[F.index(i)] = ni
        lhs = dp[(Np + ni, tuple(c))]
        rhs = lemma_rhs(coef, ni, h, -Q[i, i])
        print(f"    n_i = {ni}: P_N(n) = {lhs:.12e}  lemma = {rhs:.12e}  rel {abs(lhs/rhs-1):.1e}")

print("(3) facet functions for the 3-cycle, i = 3, against Lemma L-two")
Q, mu = CYC
fac = Facet(Q, mu, [0, 1, 2], 2)
cm, cp = fac.cm, fac.cp
for beta in ([0.5, 0.5], [0.3, 0.7]):
    for z in (0.0, 0.05, 0.08j, 0.06 * cmath.exp(2.2j)):
        J, C = fac.JC(np.array(beta), z)
        a12 = 2 + z * cm[0] * cp[1]
        a21 = 1 + z * cm[1] * cp[0]
        vp = a12 * a21
        d = fac.d(z)
        Jc = d @ np.array(beta) - 2 * cmath.sqrt(beta[0] * beta[1] * vp)
        p = fac.muG + z * fac.mui * cp
        e = 1 + z * cm
        U = p[0] * e[0] * cmath.sqrt(vp * beta[0] / beta[1]) + p[1] * e[1] * cmath.sqrt(vp * beta[1] / beta[0])
        V = p[0] * a12 * e[1] + p[1] * a21 * e[0]
        Cc = (U + V) / (math.sqrt(4 * math.pi) * (vp * beta[0] * beta[1]) ** 0.25)
        print(f"  beta={beta} z={complex(z):.3f}: |dJ| {abs(J-Jc):.1e} |dC/C| {abs(C/Cc-1):.1e}")
print(f"  omega at beta=(1/2,1/2): {fac.omega([0.5,0.5]):.12f}  paper 2+9/4*sqrt2 = {2+2.25*math.sqrt(2):.12f}")
