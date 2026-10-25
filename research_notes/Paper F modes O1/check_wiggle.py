# check_wiggle.py -- (LR)-type wiggles in f_+ at a scale w >> B_N pass into
# the big-jump zone of P_N and create extra local extrema there.
# f_+(n) = c n^(-5/2) (1 + eps sin(2 pi n / w)) for n >= 1, minus law zeta 3/2.
# Paper F (problem 131), modal structure (O1).
# Run: py -I check_wiggle.py
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from scipy.special import zeta as hz
from engine import zeta_law, law_from_f, build, law_N, sign_changes

alpha = 1.5
s = alpha + 1


def wiggle_law(nmax, eps, w):
    M = 4_000_000
    nn = np.arange(1, M + 1, dtype=float)
    base = nn ** (-s)
    wig = base * (1 + eps * np.sin(2 * np.pi * nn / w))
    tot = wig.sum() + (hz(s, M + 1))  # tail of the sine part averages out
    f = np.zeros(nmax + 2)
    f[1:] = wig[: nmax + 1] / tot
    # tail T(m) = 1 - sum_{n<m} f(n)
    return law_from_f(f)


n = 3000
fm, Tm = zeta_law(alpha, n)
CASES = [(0.0, 60), (0.3, 60), (0.3, 300), (0.05, 300), (0.3, 600), (0.3, 1000), (0.1, 30)]
for eps, w in CASES:
    fp, Tp = wiggle_law(n, eps, w) if eps > 0 else zeta_law(alpha, n)
    S0 = np.zeros((n + 1, n + 1)); S0[0, 0] = 1.0
    S, E = build(fp, fm, n, S0, None)
    for N in (1500, 3000):
        P = law_N(S, E, Tp, Tm, N)
        sc = sign_changes(P)[0]
        mono = bool((np.diff(fp[N // 4 : N]) < 0).all())
        print("eps=%.2f w=%d N=%d: %d sign changes; f_+ decreasing on [N/4,N]: %s; changes at: %s"
              % (eps, w, N, len(sc), mono, sc))
