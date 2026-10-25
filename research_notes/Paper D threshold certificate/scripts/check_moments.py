"""Consistency checks of the moment input (exact or ball arithmetic).

Checks, for several rational a in (1/2, 1):
  * m_2 = a/(2a-1) and m_3 = (a+1)/(2(2a-1)), the coefficients printed in
    Guerin-Laulin-Raschel-Simon (4), from the recursion (12) in exact rationals;
  * E[L] = 1/Gamma(1+a) (Janson; Bercu) and E[L^2] = 1/((2a-1) Gamma(2a)) (Bercu;
    GLR Thm 2.1) from E[L^n] = n! m_n / Gamma(1+an), in ball arithmetic;
  * the bound m_n <= A B^n of Lemma 1 for n <= N (asserted inside erw_cf.ERW).
Run: py -I check_moments.py
"""
import sys
from fractions import Fraction

sys.path.insert(0, ".")
from flint import arb, fmpq  # noqa: E402
from erw_cf import ERW  # noqa: E402


def exact_m(a, n_max):
    m = [Fraction(1), Fraction(1)]
    for n in range(2, n_max + 1):
        s = sum((a if j % 2 else 1) * m[j] * m[n - j] for j in range(1, n))
        m.append(s / (n * a - (a if n % 2 else 1)))
    return m


ok = True
for a_str in ["0.55", "0.6688", "0.8", "0.95"]:
    a = Fraction(a_str)
    m = exact_m(a, 6)
    ok &= m[2] == a / (2 * a - 1) and m[3] == (a + 1) / (2 * (2 * a - 1))
    e = ERW(a_str, N=200, prec=300)
    ab = arb(fmpq(a.numerator, a.denominator))
    EL = e.m[1] / e.g[1]
    EL2 = 2 * e.m[2] / e.g[2]
    ok &= (EL - 1 / (1 + ab).gamma()).contains(0)
    ok &= (EL2 - 1 / ((2 * ab - 1) * (2 * ab).gamma())).contains(0)
    print(a_str, "m2,m3 exact ok;", "E[L] =", EL.str(12), " E[L^2] =", EL2.str(12),
          " A =", e.A.str(6), " B =", e.B.str(6))
print("all checks passed" if ok else "CHECK FAILED")
sys.exit(0 if ok else 1)
