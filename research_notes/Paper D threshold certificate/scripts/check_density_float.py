"""Float-level sanity check (evidence only, nothing certified).

Compares the density f_a(x) obtained by Fourier inversion of the moment series
phi_a (trapezoid rule on [0, 16]) with the exact finite-n mass function of the
walk started with a plus step, rescaled as n^a/2 P(S_n = j) at j ~ x n^a
(Trinas-Valle local limit theorem).  Default a = 0.6688, n = 8000.
Run: py -I check_density_float.py [a] [n]
"""
import sys

import numpy as np

sys.path.insert(0, ".")
from flint import arb  # noqa: E402
from erw_cf import ERW  # noqa: E402

a_str = sys.argv[1] if len(sys.argv) > 1 else "0.6688"
n = int(sys.argv[2]) if len(sys.argv) > 2 else 8000
a = float(a_str)
e = ERW(a_str, N=1500)
ts = np.linspace(0, 16, 8001)
ph = []
for t in ts:
    r, i, _ = e.phi(arb(float(t)))
    ph.append(complex(float(r.mid()), float(i.mid())))
ph = np.array(ph)


def f(x):
    return np.trapezoid((np.exp(-1j * ts * x) * ph).real, ts) / np.pi


p = np.zeros(2 * n + 3)
off = n + 1
p[off + 1] = 1.0
for k in range(1, n):
    s = np.arange(-k, k + 1)
    idx = off + s
    q = p[idx]
    up = 0.5 + a * s / (2 * k)
    new = np.zeros_like(p)
    new[idx + 1] += q * up
    new[idx - 1] += q * (1 - up)
    p = new
print("x      f_a(x) (Fourier)   n^a/2 P(S_n=j)")
for x in [-1.0, 0.0, 0.5, 1.0, 2.0, 3.0]:
    j = int(round(x * n ** a))
    if (j - n) % 2:
        j += 1
    print("%5.2f  %.6f           %.6f" % (x, f(j / n ** a), n ** a / 2 * p[off + j]))
