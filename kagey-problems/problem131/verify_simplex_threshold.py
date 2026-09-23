"""Independent checks for the simplex threshold extension (standard library only).

Run: python -B verify_simplex_threshold.py
Outputs data/simplex-verification.json. Exact checks use word
enumeration and rational arithmetic. Large-N checks use 65-digit Decimal and a
positive refresh series; cutoff comparison is numerical, not interval-certified.
"""
from collections import Counter, defaultdict
from decimal import Decimal, localcontext
from fractions import Fraction
from itertools import product
from math import comb, factorial, ceil, log, pi
from pathlib import Path
import json


def balanced(n, k):
    a, b = divmod(n, k)
    return (a + 1,) * b + (a,) * (k - b)


def convolution(a, b, cutoff=None):
    length = len(a) + len(b) - 1
    if cutoff is not None:
        length = min(length, cutoff + 1)
    out = [a[0] * b[0] * 0 for _ in range(length)]
    for i, x in enumerate(a):
        if x:
            for j in range(min(len(b), length - i)):
                if b[j]:
                    out[i + j] += x * b[j]
    return out


def refresh_ratio(counts, u):
    v = u / (1 - u)
    coeff = [Fraction(1)]
    for n in counts:
        b = [Fraction(0)] + [Fraction(comb(n - 1, m - 1), factorial(m)) * v**m
                              for m in range(1, n + 1)]
        coeff = convolution(coeff, b)
    return (1 - u) ** (sum(counts) - 1) / v * sum(
        factorial(m) * c for m, c in enumerate(coeff))


def enumerate_polynomials(n, d):
    polynomials = defaultdict(Counter)
    for word in product(range(d), repeat=n):
        counts = tuple(word.count(i) for i in range(d))
        changes = sum(a != b for a, b in zip(word, word[1:]))
        polynomials[counts][changes] += 1
    return polynomials


def evaluate(poly, u):
    return sum(c * u**j for j, c in poly.items())


def exact_checks():
    checked, balancing, mode_cases = 0, 0, 0
    for d in range(2, 5):
        for n in range(d, 9):
            polys = enumerate_polynomials(n, d)
            for k in range(2, d + 1):
                counts = balanced(n, k)
                poly = polys[counts + (0,) * (d - k)]
                assert poly[k - 1] == factorial(k)
                assert poly[k] == factorial(k) * (k - 1) * (n - k) // 2
                for u in (Fraction(1, 5), Fraction(1, 2)):
                    assert evaluate(poly, u) == refresh_ratio(counts, u)
                    checked += 1
            for u in (Fraction(1, 5), Fraction(7, 20), Fraction(1, 2)):
                scores = {a: evaluate(poly, u) for a, poly in polys.items()}
                for counts, value in scores.items():
                    for a in range(d):
                        for b in range(d):
                            if counts[a] > 0 and counts[b] >= counts[a] + 2:
                                new = list(counts)
                                new[a] += 1
                                new[b] -= 1
                                assert scores[tuple(new)] > value
                                balancing += 1
                candidates = [scores[balanced(n, k) + (0,) * (d-k)]
                              for k in range(1, min(d, n) + 1)]
                assert max(candidates) == max(scores.values())
                mode_cases += 1
    u = Fraction(7, 20)
    edge = refresh_ratio((2, 2), u)
    center = refresh_ratio((2, 1, 1), u)
    assert edge == Fraction(4123, 4000)
    assert center == Fraction(3969, 4000)
    assert center < 1 < edge
    return {"enumeration_vs_refresh_comparisons": checked,
            "strict_balancing_comparisons": balancing,
            "global_maximum_reductions": mode_cases,
            "finite_size_counterexample": {"d": 3, "N": 4, "p": "10/17",
                "edge_vertex_ratio": str(edge), "full_center_vertex_ratio": str(center)}}


def positive_coefficients(n, k, cutoff, counts=None):
    """Coefficients of the finite counterpart of F_k(x), scaled by M!."""
    h = Decimal(n) / k
    total = [Decimal(1)]
    for ni in (balanced(n, k) if counts is None else counts):
        single = [Decimal(0), Decimal(1)]
        for m in range(2, min(ni, cutoff) + 1):
            single.append(single[-1] * (ni - m + 1) / (h * m * (m - 1)))
        total = convolution(total, single, cutoff)
    fac = Decimal(1)
    for m in range(len(total)):
        if m:
            fac *= m
        total[m] *= fac
    return total


def log_ratio_from_coeff(n, k, coeff, z):
    u = z / n
    x = z / (k * (1 - u))
    value = Decimal(0)
    for c in reversed(coeff):
        value = value * x + c
    h = Decimal(n) / k
    return (n - 1) * (1 - u).ln() + (1 - k) * h.ln() + value.ln() - x.ln()


def root_from_coeff(n, k, coeff):
    lo = Decimal("1e-30")
    hi = min(Decimal("0.75") * n, 2 * Decimal(n).ln() + 3)
    assert log_ratio_from_coeff(n, k, coeff, hi) > 0
    for _ in range(135):
        mid = (lo + hi) / 2
        if log_ratio_from_coeff(n, k, coeff, mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def numerical_checks():
    rows = []
    # 70 digits is ample here; these are numerical consistency checks only.
    with localcontext() as ctx:
        ctx.prec = 70
        # Supply pi independently to more precision than any displayed result.
        pi_d = Decimal("3.141592653589793238462643383279502884197169399375105820974944592307816")
        for k in (2, 3, 4, 5):
            ak = (4 * pi_d).ln() / 2 - (Decimal(k) + Decimal("0.5")) * Decimal(k).ln() / (k - 1)
            prior = Decimal(1)
            for n in (30, 100, 1000, 10000, 1000000):
                cutoff = min(n, ceil(5 * k * (log(n) + 1)))
                coeff = positive_coefficients(n, k, cutoff)
                z = root_from_coeff(n, k, coeff)
                assert z / n < prior
                prior = z / n
                L = Decimal(n).ln()
                second = L - L.ln() / 2 + ak
                third = second + (L.ln() / 4 - ak / 2 + Decimal(1) / 8) / L
                test_z = L - L.ln() / 2 + Decimal("0.2")
                if test_z > 0:
                    lr = log_ratio_from_coeff(n, k, coeff, test_z)
                    limiting_lr = (k - 1) * (Decimal("0.2") - ak)
                    profile_error = lr - limiting_lr
                else:
                    profile_error = None
                # Independent wider cutoff comparison for the largest N of each k.
                cutoff_difference = None
                if n == 1000000:
                    larger = positive_coefficients(n, k, cutoff + 40)
                    z_more = root_from_coeff(n, k, larger)
                    cutoff_difference = abs(z - z_more)
                    assert cutoff_difference < Decimal("1e-30")
                rows.append({"k": k, "N": n, "cutoff": cutoff,
                             "Nu_root": str(z), "a_k": str(ak),
                             "second_order_error": str(z-second),
                             "third_order_error": str(z-third),
                             "window_log_ratio_error_at_t_0.2": str(profile_error),
                             "wider_cutoff_root_difference": str(cutoff_difference)})
    return rows


def general_composition_checks():
    rows = []
    with localcontext() as ctx:
        ctx.prec = 70
        pi_d = Decimal("3.141592653589793238462643383279502884197169399375105820974944592307816")
        for weights in ((2, 8), (2, 3, 5), (1, 2, 3, 4)):
            k = len(weights)
            alpha = [Decimal(w) / sum(weights) for w in weights]
            A = sum(a.sqrt() for a in alpha)
            g = A * A - 1
            s = Decimal(k - 1)
            log_D = ((Decimal(k) / 2 + 1) * A.ln()
                     - Decimal("0.75") * sum(a.ln() for a in alpha)
                     - s / 2 * (4 * pi_d).ln())
            for n in (100, 10000, 1000000):
                counts = tuple(n * w // sum(weights) for w in weights)
                assert sum(counts) == n
                cutoff = min(n, ceil(5 * k * (log(n) + 1)))
                coeff = positive_coefficients(n, k, cutoff, counts)
                z = root_from_coeff(n, k, coeff)
                L = Decimal(n).ln()
                predicted = (s / g * L - s / (2 * g) * L.ln()
                             - (log_D + s / 2 * (s / g).ln()) / g)
                rows.append({"counts": counts, "N": n, "Nu_root": str(z),
                             "leading_coefficient": str(s/g),
                             "constant_order_prediction_error": str(z-predicted)})
    return rows


if __name__ == "__main__":
    result = {"status": "passed", "exact": exact_checks(),
              "numerical_scope": "70-digit Decimal; positive-series truncation; not interval-certified",
              "threshold_checks": numerical_checks(),
              "general_composition_checks": general_composition_checks()}
    path = Path(__file__).resolve().parent / "data" / "simplex-verification.json"
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "exact": result["exact"],
                      "large_N_cases": len(result["threshold_checks"]),
                      "general_composition_cases": len(result["general_composition_checks"]),
                      "output": str(path)}, indent=2))
