# check_prepared.py -- prepared initial runs (Theorem C kernels) with the
# log-convex zeta law: does the preparation change the modal structure?
# Paper F (problem 131), modal structure (O1).
# Run: py -I check_prepared.py
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from scipy.special import zeta as hz
from engine import zeta_law, build, law_N, renewal, sign_changes

alpha = 1.5
n = 3000
f, T = zeta_law(alpha, n)
mu = hz(alpha, 1) / hz(alpha + 1, 1)
u = renewal(f, n)


def local_max(P):
    """indices of local maxima of P on {0..N} (endpoints compared with their
    single neighbour); plateaus are reported at their left end."""
    out = []
    N = len(P) - 1
    for k in range(N + 1):
        l = P[k - 1] if k > 0 else -1.0
        r = P[k + 1] if k < N else -1.0
        if P[k] > l and P[k] >= r and P[k] > 0:
            out.append(k)
    return out


print("== P6: plus fresh w.p. 1/2, minus of length 5 w.p. 1/2 ==")
kap = np.zeros(40)
kap[0] = 0.5
for j in range(1, 40):
    kap[j] = 0.5 * u[j] + (0.5 * u[j - 5] if j >= 5 else 0.0)
print("profile kappa(0..8):", np.round(kap[:9], 4))
S0 = np.zeros((n + 1, n + 1)); E0 = np.zeros((n + 1, n + 1))
S0[0, 0] = 0.5; S0[0, 5] = 0.5
S, E = build(f, f, n, S0, E0)
for N in (200, 1000, 3000):
    P = law_N(S, E, T, T, N, Qp=0.0, Qm=(0.5 if N <= 5 else 0.0))
    lm = local_max(P)
    print("N=%d local maxima at k=%s ; N-k for the top ones: %s" % (N, lm, [N - k for k in lm if k > N / 2]))
    R = P[::-1] / T[N]
    print("   R_N(0..8) =", np.round(R[:9], 4))

print("== P7: minus initial run, nu_-(d) = T(d)/(mu-1), d >= 2 ==")
nu = np.zeros(n + 2)
nu[2:] = T[2:] / (mu - 1.0)
# Q_-(N) = sum_{d >= N} nu(d) = (sum_{d>=N} T(d))/(mu-1); sum_{d>=N}T(d) via
# sum_{d>=N} T(d) = sum_{n>=N} (n-N+1) f(n) = mean-type Hurwitz expression
def tailsumT(N):
    s = alpha + 1
    # sum_{n>=N} (n - N + 1) n^{-s} / zeta(s)
    return (hz(s - 1, N) - (N - 1) * hz(s, N)) / hz(s, 1)
kap = np.zeros(400)
for j in range(2, 400):
    kap[j] = nu[2 : j + 1] @ u[j - 2 :: -1][: j - 1]
dk = np.diff(kap[2:])
print("kappa(2..10):", np.round(kap[2:11], 5), " 1/mu =", round(1 / mu, 5))
print("Delta kappa >0 for all j in [2,399):", bool((dk > 0).all()),
      "; ratio Delta kappa * mu^2 / T at j=300:", dk[297] * mu ** 2 / T[300],
      " predicted c*mu-1 =", mu / (mu - 1) - 1)
S0 = np.zeros((n + 1, n + 1)); E0 = np.zeros((n + 1, n + 1))
S0[0, 2:] = nu[2 : n + 1]
S, E = build(f, f, n, S0, E0)
for N in (500, 1000, 2000, 3000):
    P = law_N(S, E, T, T, N, Qp=0.0, Qm=tailsumT(N) / (mu - 1.0))
    lm = local_max(P)
    R = P[::-1]
    jmin = 1 + int(np.argmin(R[1 : N // 2][R[1 : N // 2] > 0])) if False else None
    sc = sign_changes(P, N // 2, N)[0]
    print("N=%d local maxima at k=%s ; sign changes of Delta P on k>N/2: %s" % (N, lm, sc))
