# check_pair.py -- predictions P3, P4, P6 for a pair face (k = 2).
# F = {j, i} with q_ji = 1, q_ij = 2, start (0.6, 0.4). R = P_N(n)/P_N'(n-hat)
# from the exact discrete Pedler sum (verified against the recursion below),
# the Laguerre kernel L, the explicit two-sided bound of the pair-face theorem,
# and the continuum kernel h K(x, S) at x = h n_i and x = h (n_i - 1).
# Paper C1 (problem 131), boundary layer at a facet, item O1.
# Run: py -I check_pair.py
import os, sys, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from scipy.special import ive
from dl_lib import make_chain, dp_face

qji, qij, muj, mui = 1.0, 2.0, 0.6, 0.4
qj, qi = qji, qij
om = qji * qij
c = [1.0, qji + mui / muj * qij, mui / muj * om]


def lcomb(a, b):
    return math.lgamma(a + 1) - math.lgamma(b + 1) - math.lgamma(a - b + 1)


def exact_R(ni, Np, h):
    pi_, pj = 1 - h * qi, 1 - h * qj
    tot = 0.0
    for K in range(1, ni + 1):
        la = lcomb(ni - 1, K - 1) + (ni - K) * math.log(pi_)
        for e in range(3):
            mm = K - e
            if mm < 0 or mm > Np - 1 or c[e] == 0:
                continue
            tot += c[e] * math.exp(la + e * math.log(h) + lcomb(Np - 1, mm)
                                   + mm * math.log(h * h * om / pj))
    return tot


def lag_L(ni, Np, h):
    S = h * Np
    pi_ = 1 - h * qi
    tot = 0.0
    for K in range(1, ni + 1):
        la = lcomb(ni - 1, K - 1) + (ni - K) * math.log(pi_) + K * math.log(h)
        for e in range(3):
            mm = K - e
            if mm < 0:
                continue
            tot += c[e] * math.exp(la + mm * math.log(S * om) - math.lgamma(mm + 1))
    return tot


def hK(x, S, h):
    if x == 0:
        return h * (S * om + c[1])
    zeta = 2 * math.sqrt(om * S * x)
    sc = math.exp(zeta - qi * x)
    I0, I1 = ive(0, zeta) * sc, ive(1, zeta) * sc
    return h * (math.sqrt(om * S / x) * I1 + c[1] * I0 + c[2] * math.sqrt(x / (om * S)) * I1)


def bound(ni, Np, h):
    S = h * Np
    U = om * S * h * ni / (1 - h * qi)
    return -(U + 2 * math.sqrt(U) + 2) / (2 * Np), math.exp(2 * h * qj * (1 + 2 * math.sqrt(U))) - 1


# exact formula against the recursion
Q, mu = make_chain({(0, 1): qji, (1, 0): qij}, [muj, mui])
Np, h = 60, 0.12
read = {Np + ni: [(Np, ni)] for ni in range(0, 9)}
dp = dp_face(Q, mu, h, [0, 1], [Np, 8], read)
P0 = dp[(Np, (Np, 0))]
print(f"exact discrete Pedler vs recursion (N' = {Np}, h = {h}):",
      max(abs(dp[(Np + ni, (Np, ni))] / P0 / exact_R(ni, Np, h) - 1) for ni in range(1, 9)))


def row(ni, Np, T):
    h = T / Np
    S = T
    R = exact_R(ni, Np, h)
    L = lag_L(ni, Np, h)
    lo, hi = bound(ni, Np, h)
    e = R / L - 1
    ok = lo - 1e-15 <= e <= hi + 1e-15
    b1 = R / hK(h * ni, S, h) - 1
    b0 = R / hK(h * (ni - 1), S, h) - 1
    N = Np + ni
    print(f"{Np:8d} {T:8.2f} {ni:7d} {T*T/N:8.4f} {e:+.3e} [{lo:+.1e},{hi:+.1e}] {'ok' if ok else 'FAIL'}"
          f"  {b1:+.3e}  {b0:+.3e}")


hdr = f"{'N_prime':>8s} {'T=S':>8s} {'n_i':>7s} {'T^2/N':>8s} {'R/L-1':>10s} {'bound':>17s}     {'R/hK(hn_i)-1':>12s} {'R/hK(h(n_i-1))-1':>14s}"
print("\nA. fixed T, N' growing (T <= N^{1/3} range and beyond)")
print(hdr)
for T in (5.0, 20.0):
    for Np in (1000, 10000, 100000):
        for ni in (1, 2, 5, 20, Np // 50):
            row(ni, Np, T)
print("\nB. lattice regime T = sqrt(N')")
print(hdr)
for Np in (100, 1000, 10000, 100000):
    for ni in (1, 2, 3, 6):
        row(ni, Np, math.sqrt(Np))
