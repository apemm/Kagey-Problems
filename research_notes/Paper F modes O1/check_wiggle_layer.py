# check_wiggle_layer.py -- wiggles of f_+ near the antimode (layer side).
# f_+(n) = c n^(-5/2) (1 + eps sin(2 pi n / w)), minus law zeta 3/2, fresh plus.
# Counts local extrema of j -> P_N(N-j) on 1 <= j <= J.
# Paper F (problem 131), modal structure (O1).
# Run: py -I check_wiggle_layer.py
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from scipy.special import zeta as hz
from engine import zeta_law, law_from_f, layer_R, sign_changes

alpha = 1.5; s = alpha + 1


def wiggle_law(nmax, eps, w):
    M = 4_000_000
    nn = np.arange(1, M + 1, dtype=float)
    wig = nn ** (-s) * (1 + eps * np.sin(2 * np.pi * nn / w))
    tot = wig.sum() + hz(s, M + 1)
    f = np.zeros(nmax + 2); f[1:] = wig[: nmax + 1] / tot
    return law_from_f(f)


for eps, w in ((0.0, 1), (0.3, 60), (0.1, 60), (0.3, 20), (0.03, 60)):
    for N in (1500, 3000, 6000, 10000):
        fm, Tm = zeta_law(alpha, N)
        fp, Tp = (wiggle_law(N, eps, w) if eps > 0 else (fm, Tm))
        J = int(0.5 * N ** (1 / alpha))
        R = layer_R(fp, Tp, fm, Tm, N, J)
        sc = sign_changes(R, 1, J)[0]
        print("eps=%.2f w=%3d N=%5d J=%4d: extrema of P_N(N-j), 1<=j<J, at %s" % (eps, w, N, J, sc))
