# check04_full.py -- predictions R3, R4, R5, R6 of 04_predictions.md, from the
# full exact law (exact04.py), cross-checked against engine.py at N = 400.
#   R3: convexity of j -> P_N(N-j) from the plus end into the bulk (fresh plus).
#   R4: D_N(j) > 0 on the big-jump zone and D_N / dG -> 1 (fresh plus).
#   R5: bulk, fair start: B_N^2 Delta P_N vs h'(x), B_N^3 Delta^2 P_N vs h''(x).
#   R6: law conditioned on runs >= 2, fair start: number of modes for
#       N = 1000..4000, positions of the extrema near the plus end, and the
#       sign of the second difference there.
# Zeta law f(n) = n^(-5/2)/zeta(5/2) for both signs (runs >= 2: n >= 2).
# Paper F (problem 131), modal structure (O1).
# Run: py -I check04_full.py   (about two minutes, about 0.5 GB of memory)
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from scipy.special import zeta as hz, gamma as Gam
from scipy.integrate import quad
from exact04 import zeta_law, rows, P_at, renewal, modes, minima

alpha = 1.5
NMAX = 4000


def laws(fp, Tp, fm, Tm, Ns, wp, wm):
    S, E = rows(fp, fm, NMAX, NMAX, wp, wm)
    out = {N: np.array([P_at(S, E, Tp, Tm, N, k) for k in range(N + 1)]) for N in Ns}
    del S, E
    return out


f, T = zeta_law(alpha, NMAX + 2)
mu = hz(alpha, 1) / hz(alpha + 1, 1)
s = 2 * mu; p = 0.5
cT = 1.0 / (alpha * hz(alpha + 1, 1))                  # T(x) ~ cT x^-alpha
a = lambda t: (cT * t) ** (1 / alpha)
fc = lambda x: x ** (-alpha - 1) / hz(alpha + 1, 1)    # f at real arguments

# --- independence check against engine.py ---
from engine import build, law_N
S0 = np.zeros((401, 401)); S0[0, 0] = 1.0
Se, Ee = build(f, f, 400, S0=S0)
Pe = law_N(Se, Ee, T, T, 400)
S, E = rows(f, f, 400, 400, 1.0, 0.0)
Pm = np.array([P_at(S, E, T, T, 400, k) for k in range(401)])
print("engine.py vs exact04.py, fresh plus, N=400: max diff %.1e" % abs(Pe - Pm).max())

Ns = (1000, 2000, 4000)
plus = laws(f, T, f, T, Ns, 1.0, 0.0)
fair = laws(f, T, f, T, Ns, 0.5, 0.5)

# stable profile for equal laws: W = (Z+ - Z-)/2, log E e^{itW} = -c|t|^alpha
K = -Gam(1 - alpha)
c = -2 * K * np.cos(np.pi * alpha / 2) / 2 ** alpha
h0 = lambda x: quad(lambda t: np.cos(t * x) * np.exp(-c * t ** alpha), 0, np.inf, limit=400)[0] / np.pi
h1 = lambda x: -quad(lambda t: t * np.sin(t * x) * np.exp(-c * t ** alpha), 0, np.inf, limit=400)[0] / np.pi
h2 = lambda x: -quad(lambda t: t * t * np.cos(t * x) * np.exp(-c * t ** alpha), 0, np.inf, limit=400)[0] / np.pi
from scipy.optimize import brentq
xinf = brentq(h2, 0.05, 5.0)
print("profile: h(0)=%.4f, inflection of h at |x| = %.4f" % (h0(0), xinf))

print("== R3: convexity of j -> P_N(N-j), fresh plus ==")
for N in Ns:
    g = plus[N][::-1]
    d2 = g[2:] - 2 * g[1:-1] + g[:-2]
    B = a(N / s)
    bad = np.where(d2[: N // 2] <= 0)[0]
    j0 = bad[0] if len(bad) else None
    x0 = (N - j0 - 1 - p * N) / B if j0 is not None else None
    print("N=%d B_N=%.2f  first j with Delta^2 <= 0: %s  (x = %s)" %
          (N, B, j0, "%.3f" % x0 if x0 is not None else "-"))

print("== R4: big-jump zone, fresh plus: D_N > 0 and D_N / dG ==")
for N in Ns:
    P = plus[N]; B = a(N / s)
    jlo = int(N ** 0.6); jhi = int((1 - p) * N - 3 * B)
    D = np.array([P[N - j - 1] - P[N - j] for j in range(jlo, jhi + 1)])
    rat = []
    for j in (int(N ** 0.7), N // 8, N // 4, int((1 - p) * N - 10 * B), int((1 - p) * N - 5 * B)):
        L = N - j * s / mu
        dG = 2 * s * fc(L) / mu ** 2 + (j * s ** 2 / mu ** 3) * (alpha + 1) * fc(L) / L
        rat.append("j=%d(L/B=%.1f): %.3f" % (j, L / B, (P[N - j - 1] - P[N - j]) / dG))
    print("N=%d  min D_N on [N^0.6, (1-p)N-3B] = %.3e (>0: %s)   ratios: %s"
          % (N, D.min(), D.min() > 0, "  ".join(rat)))

print("== R5: bulk, fair start ==")
for N in Ns:
    P = fair[N]; B = a(N / s)
    ks = [k for k in range(N) if abs(k + 0.5 - p * N) <= 3 * B]
    e1 = max(abs(B ** 2 * (P[k + 1] - P[k]) - h1((k + 0.5 - p * N) / B)) for k in ks)
    ks2 = [k for k in range(1, N) if abs(k - p * N) <= 3 * B]
    e2 = max(abs(B ** 3 * (P[k + 1] - 2 * P[k] + P[k - 1]) - h2((k - p * N) / B)) for k in ks2)
    d = np.diff(P[ks[0]: ks[-1] + 2])
    sc = int(np.sum(np.sign(d[1:]) * np.sign(d[:-1]) < 0))
    near = [k for k in ks2 if abs(k - p * N) <= 0.5 * B]
    mx = max(P[k + 1] - 2 * P[k] + P[k - 1] for k in near)
    e0 = max(abs(B * P[k] - h0((k - p * N) / B)) for k in ks2)
    print("N=%d  sup|B P - h|=%.4f  sup|B^2 dP - h'|=%.4f (sup|h'|=%.3f)  sup|B^3 d2P - h''|=%.4f (|h''(0)|=%.3f)"
          "  sign changes on |x|<=3: %d   max Delta^2 P on |x|<=0.5: %.2e"
          % (N, e0, e1, abs(h1(xinf)), e2, abs(h2(0)), sc, mx))

print("== R6: runs >= 2, fair start ==")
del plus, fair
f2, T2 = zeta_law(alpha, NMAX + 2, nmin=2)
N6 = (1000, 1500, 2000, 2500, 3000, 3500, 4000)
r2 = laws(f2, T2, f2, T2, N6, 0.5, 0.5)
for N in N6:
    P = r2[N]
    M = modes(P); m = minima(P)
    nearp = sorted(N - k for k in M if k > N / 2)
    nearpm = sorted(N - k for k in m if k > N / 2)
    g = P[::-1]; d2 = g[2:] - 2 * g[1:-1] + g[:-2]
    win = [j for j in range(10, 80) if d2[j] <= 0]
    print("N=%d  modes=%d  maxima at distance from plus end: %s  minima: %s  "
          "j in [10,80) with Delta^2_j P(N-j) <= 0: %s"
          % (N, len(M), nearp[:12], nearpm[:12], win))
