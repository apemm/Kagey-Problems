"""Independent exact-rational tests of the certificate arithmetic."""
from decimal import localcontext
from fractions import Fraction as F
from math import comb
import unittest

from certified_decimal import I, PI, central_sum, pi_fraction_bounds, zeta_bounds, zeta_grid


def log_fraction_bounds(x, terms=180):
    """Independent atanh series, with a rational geometric remainder bound."""
    y = (x - 1) / (x + 1)
    if y < 0:
        lo, hi = log_fraction_bounds(1 / x, terms)
        return -hi, -lo
    total = 2 * sum((y ** (2 * k + 1) / (2 * k + 1)
                     for k in range(terms)), F(0))
    tail = 2 * y ** (2 * terms + 1) / ((2 * terms + 1) * (1 - y * y))
    return total, total + tail


class CertificateArithmetic(unittest.TestCase):
    def encloses(self, interval, value):
        self.assertLessEqual(F(interval.lo), value)
        self.assertGreaterEqual(F(interval.hi), value)

    def test_rational_arithmetic_and_ambient_precision(self):
        # In particular, check negative operands and cancellation at low ambient
        # precision. Decimal unary minus would silently round at that precision.
        with localcontext() as ctx:
            ctx.prec = 6
            for a in (F(-23, 7), F(-1, 3), F(0), F(1, 11), F(31, 9)):
                x = I.rational(a.numerator, a.denominator)
                self.encloses(-x, -a)
                for b in (F(-19, 13), F(1, 7), F(8, 3)):
                    y = I.rational(b.numerator, b.denominator)
                    for interval, exact in ((x + y, a + b), (x - y, a - b),
                                            (x * y, a * b), (x / y, a / b)):
                        self.encloses(interval, exact)
        x, y = I("-2.3", "1.7"), I("-0.8", "4.1")
        for a in (F("-2.3"), F(0), F("1.7")):
            for b in (F("-0.8"), F(0), F("4.1")):
                self.encloses(x * y, a * b)
        with self.assertRaises(ZeroDivisionError):
            x / y
        with self.assertRaises(TypeError):
            I(0.1)

    def test_log_against_rational_series(self):
        for x in (F(1, 3), F(1), F(7, 5), F(2), F(3)):
            bounds = I.rational(x.numerator, x.denominator).ln()
            lo, hi = log_fraction_bounds(x)
            self.encloses(bounds, lo)
            self.encloses(bounds, hi)

    def test_pi_identity_and_bounds(self):
        # tan(4 atan(1/5) - atan(1/239)) = 1 exactly.
        tangent = F(1, 5)
        for _ in range(2):
            tangent = 2 * tangent / (1 - tangent * tangent)
        self.assertEqual((tangent - F(1, 239)) / (1 + tangent / 239), 1)
        lo, hi = pi_fraction_bounds()
        self.assertLess(lo, hi)
        self.assertLess(hi - lo, F(1, 10 ** 110))
        self.encloses(PI, lo)
        self.encloses(PI, hi)

    def test_exp_against_rational_series(self):
        for x in (0, 1, 2, 4):
            total, term = F(1), F(1)
            for k in range(1, 141):
                term *= F(x, k)
                total += term
            next_term = term * F(x, 141)
            tail = next_term / (1 - F(x, 142))
            bounds = I(x).exp()
            self.encloses(bounds, total)
            self.encloses(bounds, total + tail)
            self.encloses(I(-x).exp(), 1 / total)
            self.encloses(I(-x).exp(), 1 / (total + tail))

    def test_central_sum_against_complete_exact_polynomial(self):
        # The larger examples exercise the early stop and its enclosed tail.
        for N, u in [(2, F(1, 2)), (3, F(2, 5)), (8, F(2, 7)),
                     (17, F(1, 9)), (174, F(1, 40)), (175, F(1, 40)),
                     (401, F(1, 80))]:
            a, b = N // 2, N - N // 2
            exact = sum((F(comb(a - 1, r) * comb(b - 1, r))
                         * u ** (2 * r + 1)
                         * (2 + F(N - 2 - 2 * r, r + 1) * u)
                         for r in range(a)), F(0))
            bounds = central_sum(N, I.rational(u.numerator, u.denominator))
            self.encloses(bounds, exact)
            self.assertLess(bounds.width(), I("1e-60").lo)

    def test_root_and_grid_independent_of_ambient_context(self):
        for N in (2, 15, 174, 175, 219, 2773, 2774):
            root = zeta_bounds(N)
            self.assertLess(root.width(), I("2.00001e-45").lo)
            with localcontext() as ctx:
                ctx.prec = 8
                zeta_bounds.cache_clear()
                self.assertEqual(root, zeta_bounds(N))
                a, u = zeta_grid(N, 10 ** 7)
                self.assertLess(F(a, 10 ** 7), F(u.lo))
                self.assertLess(F(u.hi), F(a + 1, 10 ** 7))


if __name__ == "__main__":
    unittest.main()
