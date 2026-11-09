"""Rigorous intervals for the Euler product and protected pressure constants."""
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction
from pathlib import Path
import json
import time

HERE = Path(__file__).resolve().parent
began = time.monotonic()
limit = 1000000
is_prime = bytearray(b"\x01")*(limit+1)
is_prime[0:2] = b"\x00\x00"
for p in range(2, int(limit**.5)+1):
    if is_prime[p]:
        start = p*p
        is_prime[start::p] = b"\x00"*(((limit-start)//p)+1)
split_primes = [p for p in range(5, limit+1, 4) if is_prime[p]]

def finite_product(rounding):
    with localcontext() as ctx:
        ctx.prec = 70
        ctx.rounding = rounding
        value = Decimal(1)
        for p in split_primes:
            numerator = (p-1)*(p*p+4*p+1)
            denominator = (p+1)**3
            value *= Decimal(numerator)/Decimal(denominator)
        return Fraction(value)

finite_lower = finite_product(ROUND_FLOOR)
finite_upper = finite_product(ROUND_CEILING)
# Sum over all integers beyond limit bounds the omitted prime tail:
# (6p+2)/(p+1)^3 <= 6/p^2 + 2/p^3.
tail = Fraction(6, limit) + Fraction(1, limit*limit)
product_lower = finite_lower*(1-tail)
product_upper = finite_upper

def atan_sum(q, terms):
    return sum((Fraction((-1)**k, (2*k+1)*q**(2*k+1))
                for k in range(terms)), Fraction())
a5lo, a5hi = atan_sum(5, 50), atan_sum(5, 51)
a239lo, a239hi = atan_sum(239, 50), atan_sum(239, 51)
pi_lower = 16*a5lo-4*a239hi
pi_upper = 16*a5hi-4*a239lo
assert pi_lower < pi_upper

def decimal_bound(value, rounding):
    with localcontext() as ctx:
        ctx.prec = 24
        ctx.rounding = rounding
        return str(Decimal(value.numerator)/Decimal(value.denominator))

def interval(lo, hi):
    assert lo <= hi
    return [decimal_bound(lo, ROUND_FLOOR), decimal_bound(hi, ROUND_CEILING)]

result = {
    "status":"PASS",
    "prime_cutoff":limit,
    "split_primes_used":len(split_primes),
    "product_P":interval(product_lower,product_upper),
    "pi":interval(pi_lower,pi_upper),
    "mixed_pressure":{},
    "total_pressure":{},
    "additive_entropy_deficit":{},
}
for name, mixed, six in [
    ("O",Fraction(32,9),Fraction(45)),
    ("C",Fraction(40,9),Fraction(324,5)),
    ("Q",Fraction(26,9),Fraction(144,5)),
]:
    lo = mixed*product_lower/pi_upper**4
    hi = mixed*product_upper/pi_lower**4
    result["mixed_pressure"][name] = interval(lo,hi)
    dlo = (six+mixed*product_lower)/pi_upper**4
    dhi = (six+mixed*product_upper)/pi_lower**4
    result["total_pressure"][name] = interval(dlo,dhi)
    result["additive_entropy_deficit"][name] = interval(dlo/2,dhi/2)
result["seconds"] = time.monotonic()-began
result["method"] = (
    "Exact prime sieve; directed 70-digit finite products; "
    "positive-product tail bounded by 6/N+1/N²; exact rational "
    "alternating arctangent bounds and Machin's identity for pi."
)
(HERE/"protected_entropy_constant_intervals.json").write_text(
    json.dumps(result,indent=2)+"\n",encoding="utf-8")
print(json.dumps(result,indent=2))

