# check_wide.py -- prediction P5 across the layer, n_i up to x = h n_i ~ T/5,
# for the 3-cycle (q12=q23=q31=2, q21=q32=q13=1, i = 3, beta = (1/2,1/2)).
# Prints E = P_N/(P_N' L) - 1 against h(1+x), T^2/N and the Schwarz-lemma
# term sqrt(x)/T^{3/2}; and the continuum-kernel form P_N/(P_N' h K(h n_i,S)) - 1.
# Paper C1 (problem 131), boundary layer at a facet, item O1.
# Run: py -I check_wide.py   (about 2 minutes)
import os, sys, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from dl_lib import make_chain, dp_face, Facet, Circle

Q, mu = make_chain({(0, 1): 2, (1, 2): 2, (2, 0): 2, (1, 0): 1, (2, 1): 1, (0, 2): 1},
                   [0.4, 0.35, 0.25])
F, i = [0, 1, 2], 2
fac = Facet(Q, mu, F, i)
beta = np.array([0.5, 0.5])
om = fac.omega(beta)
RADII = [0.03, 0.05, 0.08, 0.12, 0.18]
circles = {}
T = 8.0
nis = [1, 5, 10, 20, 40, 80]
print(f"3-cycle, T = {T}, omega_beta = {om:.6f}")
print(f"{'N_prime':>7s} {'n_i':>4s} {'x':>6s} {'E':>11s} {'h(1+x)':>8s} {'T^2/N':>7s} {'x^.5/T^1.5':>10s} {'K form':>11s}")
for Np in (200, 400):
    h = T / Np
    S = T
    nhat = [Np // 2, Np // 2]
    target = [nhat[0], nhat[1], max(nis)]
    read = {Np: [(nhat[0], nhat[1], 0)]}
    for ni in nis:
        read.setdefault(Np + ni, []).append((nhat[0], nhat[1], ni))
    dp = dp_face(Q, mu, h, F, target, read)
    P0 = dp[(Np, (nhat[0], nhat[1], 0))]
    for ni in nis:
        PN = dp[(Np + ni, (nhat[0], nhat[1], ni))]
        x = h * ni
        want = min(max(math.sqrt(x / (om * S)), 1 / S), 0.18)
        rho = min(RADII, key=lambda r: abs(math.log(r / want)))
        if rho not in circles:
            circles[rho] = Circle(fac, beta, rho)
        L = circles[rho].L_lattice(ni, S, h)
        K1 = circles[rho].K_cont(x, S)
        E = PN / (P0 * L) - 1
        print(f"{Np:7d} {ni:4d} {x:6.3f} {E:+.4e} {h*(1+x):8.4f} {T*T/(Np+ni):7.4f} {math.sqrt(x)/T**1.5:10.4f} {PN/(P0*h*K1)-1:+.4e}")
