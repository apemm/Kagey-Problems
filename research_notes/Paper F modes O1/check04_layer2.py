# check04_layer2.py -- prediction R2 of 04_predictions.md: second differences
# in the boundary layer, zeta law alpha = 3/2, fresh plus start.
#   E_N(j) = [Delta^2_j P_N(N-j) - T_+(N) Delta^2 u(j)] / [f_+(N)(T_-(j) + 1/N)]
# should stay bounded on 1 <= j <= N^(1-eta), with no growth in N.  Printed:
# max|E| over 1 <= j <= N^e for e = 0.5..0.9 (N^0.9 reaches the bulk at
# N = 1000, so the last columns are outside the layer statement); also reports
# the smallest j >= 0 at which Delta^2_j P_N(N-j) <= 0 in the computed range.
# Paper F (problem 131), modal structure (O1).
# Run: py -I check04_layer2.py   (a few minutes)
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from exact04 import zeta_law, law_layer, renewal

alpha = 1.5
for N in (1000, 3000, 6000):
    J = int(N ** 0.9) + 3
    f, T = zeta_law(alpha, N + 2)
    g = law_layer(f, T, f, T, N, J)          # g[j] = P_N(N-j)
    u = renewal(f, J + 2)
    d2g = g[2:] - 2 * g[1:-1] + g[:-2]       # index i <-> j = i: g(j+2)-2g(j+1)+g(j)
    d2u = u[2:J + 1] - 2 * u[1:J] + u[:J - 1]
    m = min(len(d2g), len(d2u))
    jj = np.arange(m)
    E = (d2g[:m] - T[N] * d2u[:m]) / (f[N] * (T[np.maximum(jj, 1)] + 1.0 / N))
    bad = np.where(d2g[:m] <= 0)[0]
    tab = []
    for e in (0.5, 0.6, 0.7, 0.8, 0.9):
        jm = min(m - 1, int(N ** e))
        tab.append("j<=N^%.1f(=%d): %.1f" % (e, jm, abs(E[1:jm + 1]).max()))
    print("N=%5d  max|E|:  " % N + "  ".join(tab),
          "| first j with Delta^2 <= 0:", bad[0] if len(bad) else "none (j<=%d)" % (m - 1))
