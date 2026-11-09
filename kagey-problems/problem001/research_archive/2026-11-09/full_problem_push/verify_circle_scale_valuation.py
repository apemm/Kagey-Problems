"""Check the exact Euler convolution and two-adic scale identities."""
from fractions import Fraction
from math import pi
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def factor(n):
    result = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0)+1
            n //= p
        p += 1
    if n > 1:
        result[n] = result.get(n, 0)+1
    return result


def r2_from_factors(factors):
    if any(p % 4 == 3 and exponent % 2 for p, exponent in factors.items()):
        return 0
    answer = 4
    for p, exponent in factors.items():
        if p % 4 == 1:
            answer *= exponent+1
    return answer


def value(nf, kf):
    combined = dict(nf)
    for p, exponent in kf.items():
        combined[p] = combined.get(p, 0)+2*exponent
    return r2_from_factors(combined)


def main():
    cap = 20000
    factors = [None]+[factor(k) for k in range(1, cap+1)]
    base = [0]+[value({}, factors[k])//4 for k in range(1, cap+1)]
    checked = 0
    for n in range(1, 201):
        nf = factors[n]
        rn = r2_from_factors(nf)
        if not rn:
            continue
        for k in range(1, 101):
            convolution = Fraction(0)
            for d in range(1, k+1):
                if k % d:
                    continue
                correction = Fraction(1)
                for p, exponent in factors[d].items():
                    if p % 4 != 1 or p not in nf:
                        correction = Fraction(0)
                        break
                    correction *= Fraction((-1)**exponent * 2*nf[p], nf[p]+1)
                convolution += base[k//d]*correction
            assert convolution == Fraction(value(nf, factors[k]), rn)
            assert value(nf, factors[k]) == value(nf, factor(2*k))
            checked += 1
    samples = []
    for n in (1, 2, 5, 25, 65, 325, 1105):
        nf = factor(n)
        rn = r2_from_factors(nf)
        weights = [0]+[value(nf, factors[k]) for k in range(1, cap+1)]
        total = sum(weights)
        categories = [sum(weights[k] for k in range(1, cap+1) if k % 2),
                      sum(weights[k] for k in range(1, cap+1) if k % 4 == 2),
                      sum(weights[k] for k in range(1, cap+1) if k % 4 == 0)]
        assert categories[0] == total-sum(weights[:cap//2+1])
        assert categories[1] == (sum(weights[:cap//2+1])-
                                 sum(weights[:cap//4+1]))
        assert categories[2] == sum(weights[:cap//4+1])
        coefficient = rn/pi
        for p, exponent in nf.items():
            if p % 4 == 1:
                coefficient *= 1-2*exponent/((exponent+1)*(p+1))
        samples.append(dict(N=n, K=cap, total=total,
                            category_totals=categories,
                            category_fractions=[v/total for v in categories],
                            leading_coefficient=coefficient))
    result = dict(status="PASS", exact_convolution_and_doubling_checks=checked,
                  samples=samples,
                  scope="Exact finite identities only. The uniform asymptotic "
                        "is proved analytically in the companion note.")
    (HERE/"circle_scale_valuation_check.json").write_text(
        json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

