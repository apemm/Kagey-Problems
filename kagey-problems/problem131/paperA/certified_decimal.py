"""Outward interval arithmetic for the finite certificates in Paper A.

Only the standard library is used. Basic operations round toward -/+ infinity.
Decimal ln and exp are correctly rounded to nearest, EVEN WHEN the context
requests directed rounding. We therefore widen each endpoint to its adjacent
representable numbers. See https://docs.python.org/3/library/decimal.html.
All contexts are private, so callers' Decimal precision does not affect bounds.
This is a numerical certificate implementation, not a Lean formalization.
"""
from dataclasses import dataclass
from decimal import (
    Context, Decimal as D, ROUND_CEILING, ROUND_FLOOR, ROUND_HALF_EVEN,
    localcontext,
)
from fractions import Fraction
from functools import lru_cache

PRECISION = 80
_DOWN = Context(prec=PRECISION, rounding=ROUND_FLOOR)
_UP = Context(prec=PRECISION, rounding=ROUND_CEILING)
_NEAR = Context(prec=PRECISION, rounding=ROUND_HALF_EVEN)


def _decimal(value):
    if not isinstance(value, (int, str, D)):
        raise TypeError("Use exact int, decimal string or Decimal, never float")
    return D(value)


@dataclass(frozen=True)
class Interval:
    lo: D
    hi: D

    def __init__(self, lo, hi=None):
        lo = _decimal(lo)
        hi = lo if hi is None else _decimal(hi)
        if not (lo.is_finite() and hi.is_finite() and lo <= hi):
            raise ValueError("Invalid finite interval")
        object.__setattr__(self, "lo", lo)
        object.__setattr__(self, "hi", hi)

    @staticmethod
    def rational(numerator, denominator=1):
        return Interval(numerator) / Interval(denominator)

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Interval) else Interval(value)

    def __add__(self, other):
        other = self.coerce(other)
        return Interval(_DOWN.add(self.lo, other.lo), _UP.add(self.hi, other.hi))

    __radd__ = __add__

    def __neg__(self):
        # Decimal unary minus applies the ambient context. copy_negate is exact.
        return Interval(self.hi.copy_negate(), self.lo.copy_negate())

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        pairs = [(a, b) for a in (self.lo, self.hi)
                 for b in (other.lo, other.hi)]
        return Interval(min(_DOWN.multiply(a, b) for a, b in pairs),
                        max(_UP.multiply(a, b) for a, b in pairs))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.coerce(other)
        if other.lo <= 0 <= other.hi:
            raise ZeroDivisionError("Interval divisor contains zero")
        return self * Interval(_DOWN.divide(D(1), other.hi),
                               _UP.divide(D(1), other.lo))

    def __rtruediv__(self, other):
        return self.coerce(other) / self

    def __pow__(self, exponent):
        if not isinstance(exponent, int) or exponent < 0:
            raise ValueError("Only nonnegative integer powers are supported")
        result = Interval(1)
        for _ in range(exponent):
            result = result * self
        return result

    def ln(self):
        if self.lo <= 0:
            raise ValueError("Logarithm needs a positive interval")
        return Interval(_NEAR.next_minus(_NEAR.ln(self.lo)),
                        _NEAR.next_plus(_NEAR.ln(self.hi)))

    def exp(self):
        return Interval(_NEAR.next_minus(_NEAR.exp(self.lo)),
                        _NEAR.next_plus(_NEAR.exp(self.hi)))

    def midpoint(self):
        """An approximation only. Never use it as an interval endpoint."""
        return _NEAR.divide(_NEAR.add(self.lo, self.hi), D(2))

    def width(self):
        return _UP.subtract(self.hi, self.lo)


I = Interval


def atan_inverse_bounds(q, terms=80):
    """Exact alternating-series enclosure of atan(1/q), q > 1."""
    if not isinstance(q, int) or q <= 1 or terms < 1:
        raise ValueError("Need integer q > 1 and a positive term count")
    total = sum((Fraction((-1) ** k, (2 * k + 1) * q ** (2 * k + 1))
                 for k in range(terms)), Fraction(0))
    following = total + Fraction((-1) ** terms,
                                 (2 * terms + 1) * q ** (2 * terms + 1))
    return min(total, following), max(total, following)


def pi_fraction_bounds():
    # Machin's identity: pi = 16 atan(1/5) - 4 atan(1/239).
    a, b = atan_inverse_bounds(5)
    c, d = atan_inverse_bounds(239)
    return 16 * a - 4 * d, 16 * b - 4 * c


_PI_LO, _PI_HI = pi_fraction_bounds()
PI = I(I.rational(_PI_LO.numerator, _PI_LO.denominator).lo,
       I.rational(_PI_HI.numerator, _PI_HI.denominator).hi)
C0 = (PI / 8).ln() / 2


@lru_cache(maxsize=None)
def zeta_bounds(N):
    """Enclose the unique positive root z + log(z)/2 = log(N) + C0.

    Newton's method only proposes a center. Endpoint interval signs prove the
    enclosure, using strict monotonicity of z + log(z)/2 for z > 0.
    """
    if not isinstance(N, int) or N < 2:
        raise ValueError("N must be an integer at least two")
    K = I(N).ln() + C0
    with localcontext(_NEAR):
        k = K.midpoint()
        z = max(D("0.5"), D(N).ln())
        for _ in range(100):
            nxt = z - (z + z.ln() / 2 - k) / (1 + 1 / (2 * z))
            if abs(nxt - z) < D("1e-70"):
                z = nxt
                break
            z = nxt
        h = D("1e-45")
        lo, hi = _DOWN.subtract(z, h), _UP.add(z, h)
    left, right = I(lo), I(hi)
    if not (lo > 0 and (left + left.ln() / 2 - K).hi < 0
            and (right + right.ln() / 2 - K).lo > 0):
        raise ArithmeticError(f"Could not certify zeta bracket at N={N}")
    return I(lo, hi)


def zeta_grid(N, denominator):
    """Return a with a/d < u_zeta < (a+1)/d, certified at both ends."""
    z = zeta_bounds(N)
    u = z / (N - z)
    scaled = u * denominator
    a = int(scaled.lo.to_integral_value(rounding=ROUND_FLOOR))
    if not (scaled.lo > a and scaled.hi < a + 1):
        raise ArithmeticError(f"Grid separation is undecided at N={N}")
    return a, u


def certificate_margins(N, a, b, denominator=10 ** 9):
    """Enclose every non-polynomial comparison attached to a root bracket."""
    zlo = I.rational(N * a, a + denominator)
    zhi = I.rational(N * b, b + denominator)
    z = zeta_bounds(N)
    L = I(N).ln()
    upper = z + 1 / (8 * z)
    lower = upper - z * (z + 1) / N - 1 / (16 * z ** 2)
    Rlo = zlo + zlo.ln() / 2 - L - C0 - 1 / (8 * zlo)
    Rhi = zhi + zhi.ln() / 2 - L - C0 - 1 / (8 * zhi)
    nu = L - L.ln() / 2 + C0
    return {
        "upper": upper - zhi,
        "lower": zlo - lower,
        "R_upper": 1 / (16 * zhi ** 2) - Rhi,
        "R_lower": Rlo + zlo * (zlo + 1) / N,
        "log_lower": zlo - L / 2,
        "log_upper": L - zhi,
        "nu_lower": z - nu,
        "nu_upper": nu + (L.ln() - 2 * C0) / (4 * nu) - z,
        "sign": zlo - z if N <= 15 or N >= 219 else z - zhi,
    }


def threshold_gap(N):
    z = zeta_bounds(N)
    return N * (1 / (8 * z) - 1 / (16 * z ** 2)) / (z * (z + 1)) - 1


def central_sum(N, u):
    """Enclose S_N(u), including any omitted positive tail.

    For a=floor(N/2), b=N-a, let T_r=C(a-1,r)C(b-1,r)u^(2r+1).
    The r-th pair of terms is B_r=T_r[2+(N-2-2r)u/(r+1)].
    Both the bracketed factor and T_(r+1)/T_r decrease with r. Once an
    upper bound q on that ratio is below one, the remaining sum is at
    most B_r*q/(1-q). Stopping is allowed only with this enclosed tail.
    """
    if not isinstance(N, int) or N < 2:
        raise ValueError("N must be an integer at least two")
    u = I.coerce(u)
    if u.lo < 0:
        raise ValueError("The positive-tail bound requires u >= 0")
    a, b = N // 2, N - N // 2
    term, total = u, I(0)
    for r in range(a):
        block = term * (2 + I.rational(N - 2 - 2 * r, r + 1) * u)
        total += block
        if r == a - 1:
            return total
        ratio = u ** 2 * I.rational((a - 1 - r) * (b - 1 - r),
                                   (r + 1) ** 2)
        if ratio.hi < 1:
            tail = block * ratio / (1 - ratio)
            if tail.hi < D("1e-65"):
                return total + I(0, tail.hi)
        term *= ratio
    raise AssertionError("Unreachable")
