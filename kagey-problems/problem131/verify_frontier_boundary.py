"""Independent finite checks and numerical tests of the simplex boundary laws.

Uses only the Python standard library. Exact identities use integer/Fraction
arithmetic; asymptotic tests use 70-digit Decimal positive sums. Series cutoff
comparisons are numerical checks, not interval-certified analytic proofs.
Run: python -B verify_frontier_boundary.py
"""

from collections import Counter
from decimal import Decimal, localcontext
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import ceil, comb, factorial, log
from pathlib import Path
import json

from verify_simplex_threshold import (
    convolution, enumerate_polynomials, evaluate, log_ratio_from_coeff,
    positive_coefficients,
)

PI = Decimal("3.141592653589793238462643383279502884197169399375105820974944592307816")


def phi(x):
    term = total = Decimal(1)
    for j in range(1, 2000):
        term *= x / (j * (j + 1))
        total += term
        if term < total * Decimal("1e-66"):
            return total
    raise AssertionError("Phi series did not converge")


def bpoly(a, y):
    return sum(Decimal(comb(a - 1, m - 1)) * y**m / factorial(m)
               for m in range(1, a + 1))


def bprime(a, y):
    return sum(Decimal(comb(a - 1, m - 1)) * y**(m - 1) / factorial(m - 1)
               for m in range(1, a + 1))


def singleton_identity_checks():
    checked = 0
    for size in range(2, 7):
        base = enumerate_polynomials(size, 2)
        lifted = enumerate_polynomials(size + 1, 3)
        for counts, poly in base.items():
            if min(counts) == 0:
                continue
            predicted = Counter()
            for j, coefficient in poly.items():
                predicted[j + 1] += (2 + j) * coefficient
                predicted[j + 2] += (size - 1 - j) * coefficient
            assert +predicted == +lifted[counts + (1,)]
            checked += 1
    return checked


def laguerre_bessel_checks():
    checked = 0
    for a in (1, 2, 3, 10, 25, 80):
        for w in map(Decimal, ("0.0001", "0.01", "0.1", "0.5", "1", "2")):
            deficit = 1 - bpoly(a, w) / (w * phi(a * w))
            assert -Decimal("1e-60") <= deficit <= w / 2 + Decimal("1e-60")
            checked += 1
    return checked


def majorant_coefficients(counts, cutoff):
    h = Decimal(sum(counts)) / len(counts)
    total = [Decimal(1)]
    for a in counts:
        single = [Decimal(0), Decimal(1)]
        for m in range(2, cutoff + 1):
            single.append(single[-1] * a / (h * m * (m - 1)))
        total = convolution(total, single, cutoff)
    for m in range(len(total)):
        total[m] *= factorial(m)
    return total


def majorant_checks():
    rows = []
    for counts in ((1, 1), (1, 3), (1, 1, 8), (2, 3, 4), (1, 1, 2, 6),
                   (1, 20, 30), (2, 3, 400, 600)):
        n, k = sum(counts), len(counts)
        for uf in (Fraction(1, 50), Fraction(1, 10), Fraction(1, 3)):
            # The last composition uses small odds to keep the series bounded.
            if n > 100 and uf > Fraction(1, 50):
                continue
            u = Decimal(uf.numerator) / uf.denominator
            cutoff = max(120, ceil(8 * k * n * float(u)) + 60)
            exact_c = positive_coefficients(n, k, cutoff, counts)
            major_c = majorant_coefficients(counts, cutoff)
            exact_lr = log_ratio_from_coeff(n, k, exact_c, n * u)
            major_lr = log_ratio_from_coeff(n, k, major_c, n * u)
            deficit = 1 - (exact_lr - major_lr).exp()
            v = u / (1 - u)
            bound = k * (k + 1) * v + Decimal(k) / 2 * v**2 * sum(
                Decimal(a).sqrt() for a in counts)**2
            assert -Decimal("1e-55") <= deficit <= bound + Decimal("1e-55")
            rows.append({"counts": counts, "u": str(uf), "cutoff": cutoff,
                         "relative_deficit": str(deficit), "proved_bound": str(bound)})
    return rows


def root_from_coeff(counts, coefficients):
    n, k = sum(counts), len(counts)
    low, high = Decimal("1e-30"), Decimal(n).ln() * 2
    while log_ratio_from_coeff(n, k, coefficients, high) <= 0:
        high *= 2
        assert high < Decimal(n) / 2
    for _ in range(145):
        middle = (low + high) / 2
        if log_ratio_from_coeff(n, k, coefficients, middle) < 0:
            low = middle
        else:
            high = middle
    return (low + high) / 2


def boundary_prediction(counts, r):
    n = sum(counts)
    large, rare = counts[:r], counts[r:]
    m = sum(large)
    beta = [Decimal(a) / m for a in large]
    A = sum(b.sqrt() for b in beta)
    g = A*A - 1
    K, ell = len(counts) - 1, len(rare)
    H = Decimal(r - 1) / 2 + 2 * ell
    c = K / g
    L = Decimal(n).ln()
    rho = [Decimal(a) * L**2 / n for a in rare]
    logD = ((Decimal(r)/2 + 1) * A.ln()
            - Decimal("0.75") * sum(b.ln() for b in beta)
            - Decimal(r-1)/2 * (4 * PI).ln())
    constant = logD + 2 * ell * A.ln() + H * c.ln()
    constant += sum(phi(A*A*c*c*x).ln() for x in rho)
    predicted = c * L - H / g * L.ln() - constant / g
    return predicted, (A, g, H, K, logD, rho)


def boundary_cases():
    rows = []
    configurations = ((2, (1,), (1, 1)), (2, (1, 2), (1, 1)),
                      (2, ("rho=1",), (1, 1)),
                      (3, ("rho=0.5",), (1, 2, 3)))
    for r, rare_spec, weights in configurations:
        previous_error = Decimal("Infinity")
        for n in (10000, 100000000, 10**16):
            L = Decimal(n).ln()
            rare = tuple(max(1, int(Decimal(item[4:]) * n / L**2))
                         if isinstance(item, str) else item for item in rare_spec)
            m = n - sum(rare)
            large = [m * weight // sum(weights) for weight in weights]
            large[-1] += m - sum(large)
            counts = tuple(large) + rare
            cutoff = ceil(4 * len(counts) * log(n) + 60)
            coefficients = positive_coefficients(n, len(counts), cutoff, counts)
            root = root_from_coeff(counts, coefficients)
            prediction, constants = boundary_prediction(counts, r)
            A, g, H, K, logD, rho = constants
            log_model_at_root = (logD + 2*len(rare)*A.ln() + H*root.ln()
                                 - K*L + g*root
                                 + sum(phi(A*A*Decimal(a)*root**2/n).ln() for a in rare))
            assert abs(log_model_at_root) < 3/L + 5*L**2/n
            assert abs(root-prediction) < 20*L.ln()/L + 5*L**2/n
            assert abs(root-prediction) < previous_error
            previous_error = abs(root-prediction)
            wider_difference = None
            if n == 10**16:
                wider = positive_coefficients(n, len(counts), cutoff + 45, counts)
                wider_root = root_from_coeff(counts, wider)
                wider_difference = abs(root - wider_root)
                assert wider_difference < Decimal("1e-25")
            rows.append({"r": r, "counts": counts, "N": n, "rho": list(map(str, rho)),
                         "cutoff": cutoff, "Nu_root": str(root),
                         "constant_order_prediction": str(prediction),
                         "prediction_error": str(root-prediction),
                         "log_ratio_model_at_exact_root": str(log_model_at_root),
                         "wider_cutoff_root_difference": str(wider_difference)})
    return rows


@lru_cache(None)
def proper_orders(remaining, last=-1):
    if sum(remaining) == 0:
        return 1
    total = 0
    for color, amount in enumerate(remaining):
        if amount and color != last:
            updated = list(remaining)
            updated[color] -= 1
            total += proper_orders(tuple(updated), color)
    return total


def near_vertex_polynomial(b, rare):
    result = Counter()
    for multiplicities in product(*(range(1, a+1) for a in rare)):
        m = sum(multiplicities)
        ways = 1
        for a, mi in zip(rare, multiplicities):
            ways *= comb(a-1, mi-1)
        for q in range(1, min(b, m+1)+1):
            result[m+q-1] += (proper_orders((q,) + multiplicities)
                              * comb(b-1, q-1) * ways)
    return +result


def near_vertex_checks():
    exact_checks, rows = 0, []
    for rare in ((1,), (2,), (1, 1), (1, 2), (1, 1, 1), (2, 2)):
        b = 3
        counts = (b,) + rare
        enumerated = enumerate_polynomials(sum(counts), len(counts))[counts]
        assert near_vertex_polynomial(b, rare) == enumerated
        if all(a == 1 for a in rare):
            ell = len(rare)
            singleton_formula = Counter({q + ell - 1: factorial(ell) * comb(ell + 1, q)
                                          * comb(b - 1, q - 1)
                                          for q in range(1, min(b, ell + 1) + 1)})
            assert enumerated == singleton_formula
        exact_checks += 1
        low, high = Decimal(0), Decimal(2)
        for _ in range(160):
            y = (low + high)/2
            Bs = [bpoly(a, y) for a in rare]
            H = Decimal(1)
            for value in Bs:
                H *= value
            if H < 1:
                low = y
            else:
                high = y
        y = (low + high)/2
        c = y.sqrt()
        B = [bpoly(a, y) for a in rare]
        Bp = [bprime(a, y) for a in rare]
        Hp = sum(Bp[i] / B[i] for i in range(len(rare)))  # H(y)=1.
        Q = sum(Bp[i]*Bp[j]/(B[i]*B[j]) for i in range(len(rare))
                for j in range(i+1, len(rare)))
        alpha = -1-y*Q/Hp
        if len(rare) == 1:
            assert alpha == -1
        else:
            assert alpha < -1
        previous_coefficient_error = Decimal("Infinity")
        for b in (100, 10000, 1000000):
            polynomial = near_vertex_polynomial(b, rare)
            low, high = Decimal(0), 2*c/Decimal(b).sqrt()
            for _ in range(145):
                u = (low+high)/2
                if evaluate(polynomial, u) < 1:
                    low = u
                else:
                    high = u
            root = (low+high)/2
            predicted = c/Decimal(b).sqrt()+alpha/b
            assert abs((root-predicted)*Decimal(b)**Decimal("1.5")) < 6
            coefficient_error = abs(b*(root-c/Decimal(b).sqrt())-alpha)
            assert coefficient_error < previous_coefficient_error
            previous_coefficient_error = coefficient_error
            rows.append({"b": b, "rare_counts": rare, "y_root": str(y),
                         "u_root": str(root), "coefficient_of_1_over_b": str(alpha),
                         "b_to_3_over_2_times_error": str((root-predicted)*Decimal(b)**Decimal("1.5"))})
    return {"exact_run_enumeration_checks": exact_checks, "root_cases": rows}


def main():
    with localcontext() as ctx:
        ctx.prec = 70
        output = {
            "status": "passed",
            "scope": "Exact finite identities; 70-digit Decimal asymptotic consistency tests; not interval certification",
            "singleton_coefficient_identities": singleton_identity_checks(),
            "laguerre_bessel_inequalities": laguerre_bessel_checks(),
            "uniform_majorant_cases": majorant_checks(),
            "mixed_boundary_cases": boundary_cases(),
            "near_vertex": near_vertex_checks(),
        }
    path = Path(__file__).resolve().parent / "data" / "frontier-boundary-verification.json"
    path.write_text(json.dumps(output, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"status": output["status"],
                      "singleton_identities": output["singleton_coefficient_identities"],
                      "laguerre_bessel_inequalities": output["laguerre_bessel_inequalities"],
                      "majorant_cases": len(output["uniform_majorant_cases"]),
                      "mixed_boundary_cases": len(output["mixed_boundary_cases"]),
                      "near_vertex_cases": len(output["near_vertex"]["root_cases"]),
                      "output": str(path)}, indent=2))


if __name__ == "__main__":
    main()
