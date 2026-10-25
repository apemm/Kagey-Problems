# check_facet.py -- predictions P2, P5, P6, P7 for facets with 2 and 3 states.
# Exact P_N(n) and P_N'(n-hat) from the transfer-matrix recursion; the lattice
# kernel L_beta(n_i,N') and the continuum kernel K_beta(x,S) by the contour
# integral with J_G(beta,z), C_G(beta,z) continued to complex z.
# Columns: E = P_N/(P_N' L) - 1, the lattice-vs-continuum ratios
# L/(h K(h n_i,S)) - 1 and L/(h K(h(n_i-1),S)) - 1, and the radius check.
# Paper C1 (problem 131), boundary layer at a facet, item O1.
# Run: py -I check_facet.py            (about 10 minutes)
#      py -I check_facet.py --quick    (smaller N', about 1 minute)
import os, sys, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from dl_lib import make_chain, dp_face, Facet, Circle

QUICK = "--quick" in sys.argv
CYC = make_chain({(0, 1): 2, (1, 2): 2, (2, 0): 2, (1, 0): 1, (2, 1): 1, (0, 2): 1},
                 [0.4, 0.35, 0.25])
R4 = {(0, 1): 2.0, (0, 2): 0.5, (0, 3): 1.0, (1, 0): 0.5, (1, 2): 1.5, (1, 3): 0.7,
      (2, 0): 1.0, (2, 1): 0.4, (2, 3): 1.2, (3, 0): 0.8, (3, 1): 1.6, (3, 2): 0.6}
FOUR = make_chain(R4, [0.3, 0.3, 0.2, 0.2])

RADII = [0.03, 0.05, 0.08, 0.12, 0.18]

EXAMPLES = [
    dict(name="3-cycle, i = 3, beta = (1/2,1/2)", chain=CYC, F=[0, 1, 2], i=2,
         beta_num=[1, 1], Nps=[100, 200, 400] if QUICK else [100, 200, 400, 800],
         Ts=[4.0, 8.0, 16.0], nis=[1, 2, 3, 5, 8, 12]),
    dict(name="4-state face, i = 4, beta = (1/3,1/3,1/3)", chain=FOUR, F=[0, 1, 2, 3], i=3,
         beta_num=[1, 1, 1], Nps=[60, 120] if QUICK else [60, 120, 180],
         Ts=[3.0, 6.0, 8.0], nis=[1, 2, 3, 5, 8]),
]

for ex in EXAMPLES:
    Q, mu = ex["chain"]
    F, i = ex["F"], ex["i"]
    fac = Facet(Q, mu, F, i)
    bsum = sum(ex["beta_num"])
    beta = np.array(ex["beta_num"], float) / bsum
    om = fac.omega(beta)
    circles = {}
    print(f"\n{ex['name']}: omega_beta = {om:.6f}, q_i = {fac.qi}")
    print(f"{'N_prime':>7s} {'T':>5s} {'n_i':>4s} {'1/T':>7s} {'T^2/N':>7s} {'E':>11s}"
          f" {'L/hK(hn)-1':>11s} {'L/hK(h(n-1))-1':>14s} {'radius chk':>10s} {'P_N/P_Nprime':>12s} {'h K(hn,S)':>11s}")
    for Np in ex["Nps"]:
        nhat = [Np * b // bsum for b in ex["beta_num"]]
        assert sum(nhat) == Np
        G = fac.G
        nimax = max(ex["nis"])
        target = [0] * len(F)
        for a, s in enumerate(G):
            target[F.index(s)] = nhat[a]
        target[F.index(i)] = nimax
        for T in ex["Ts"]:
            h = T / Np
            S = h * Np
            read = {}
            for ni in [0] + ex["nis"]:
                cnt = list(target)
                cnt[F.index(i)] = ni
                read.setdefault(Np + ni, []).append(tuple(cnt))
            t0 = time.time()
            dp = dp_face(Q, mu, h, F, target, read)
            cnt0 = list(target)
            cnt0[F.index(i)] = 0
            P0 = dp[(Np, tuple(cnt0))]
            for ni in ex["nis"]:
                cnt = list(target)
                cnt[F.index(i)] = ni
                PN = dp[(Np + ni, tuple(cnt))]
                x = h * ni
                want = max(math.sqrt(x / (om * S)), 1.0 / S)
                rho = min(RADII, key=lambda r: abs(math.log(r / want)))
                rho2 = RADII[max(0, RADII.index(rho) - 1)] if rho != RADII[0] else RADII[1]
                for r in (rho, rho2):
                    if r not in circles:
                        circles[r] = Circle(fac, beta, r)
                L = circles[rho].L_lattice(ni, S, h)
                L2 = circles[rho2].L_lattice(ni, S, h)
                K1 = circles[rho].K_cont(x, S)
                K0 = circles[rho].K_cont(h * (ni - 1), S)
                E = PN / (P0 * L) - 1
                N = Np + ni
                print(f"{Np:7d} {T:5.1f} {ni:4d} {1/T:7.4f} {T*T/N:7.4f} {E:+.4e}"
                      f" {L/(h*K1)-1:+.4e} {L/(h*K0)-1:+.4e}    {abs(L2/L-1):.1e} {PN/P0:12.5e} {h*K1:11.5e}")
            sys.stdout.flush()
