# check04_renewal_bigjump.py -- predictions R1 and R7 of 04_predictions.md.
# R1: Delta^2 u(j) mu^2 / f(j) -> 1 (second-difference renewal theorem).
# R7: [f^{*m}(n-1) - f^{*m}(n)] / [m (alpha+1) f(L)/L] -> 1, L = n - m mu,
#     as K = L/a(m) grows (local big jump at the level of differences).
# Paper F (problem 131), modal structure (O1).
# Run: py -I check04_renewal_bigjump.py   (about a minute)
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from exact04 import zeta_law, renewal
from scipy.special import zeta as hz

alpha = 1.5
print("== R1: Delta^2 u(j) mu^2 / f(j) ==")
for nmin in (1, 2):
    J = 20001
    f, T = zeta_law(alpha, J + 2, nmin)
    mu = hz(alpha, nmin) / hz(alpha + 1, nmin)   # exact mean
    u = renewal(f, J + 1)
    d2 = u[2:] - 2 * u[1:-1] + u[:-2]          # d2[i] = Delta^2 u at j = i+1
    jj = np.arange(1, J + 1)
    with np.errstate(divide='ignore'):
        ratio = d2 * mu ** 2 / f[1:J + 1]
    sgn = np.sign(d2)
    last = max(i + 1 for i in range(len(sgn) - 1) if sgn[i] != sgn[i + 1]) if nmin == 2 else None
    print("nmin=%d mu=%.5f" % (nmin, mu),
          " ".join("j=%d: %.4f" % (j, ratio[j - 1]) for j in (10, 100, 1000, 10000, 20000)),
          "| last sign change of Delta^2 u at j =", last)

print("== R7: local big jump for first differences ==")
f, T = zeta_law(alpha, 60000)
mu = hz(alpha, 1) / hz(alpha + 1, 1)
c = 1.0 / (alpha * hz(alpha + 1, 1))       # T(x) ~ c x^-alpha
a = lambda m: (c * m) ** (1 / alpha)       # m T(a(m)) -> 1
for m in (10, 100, 1000):
    nmax = int(m * mu + 90 * a(m)) + 10
    V = f[:nmax + 1].copy(); V[0] = 0.0
    P = np.zeros(nmax + 1); P[0] = 1.0
    base = V.copy(); e = m
    while e:                                   # binary powering, direct sums
        if e & 1:
            P = np.convolve(P, base)[:nmax + 1]
        e >>= 1
        if e:
            base = np.convolve(base, base)[:nmax + 1]
    out = []
    for K in (2, 5, 10, 20, 40, 80):
        n = int(round(m * mu + K * a(m)))
        if n > nmax:
            continue
        L = n - m * mu
        pred = m * (alpha + 1) * f[int(round(L))] / L
        out.append("K=%d: %.3f" % (K, (P[n - 1] - P[n]) / pred))
    print("m=%5d a(m)=%.1f  " % (m, a(m)) + "  ".join(out))
