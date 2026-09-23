"""Checks for the uniform growing-rare-count root theorem.

Exact checks use Fraction arithmetic and independent word enumeration.
Large examples use 100-digit Decimal arithmetic. Truncated positive sums
are compared at two cutoffs; these numerical tests are not interval proofs.
Only the Python standard library is required.
"""

from decimal import Decimal, localcontext
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import json

from verify_simplex_threshold import convolution, enumerate_polynomials, evaluate


def rare_coefficients(counts, scalar=Fraction, cutoff=None):
    out = [scalar(1)]
    for a in counts:
        top = a if cutoff is None else min(a, cutoff)
        single = [scalar(0), scalar(1)]
        for m in range(2, top + 1):
            single.append(single[-1] * (a - m + 1) / (m * (m - 1)))
        out = convolution(out, single, cutoff)
    return out


def polynomial(coefficients, y):
    out = y * 0
    for coefficient in reversed(coefficients):
        out = out * y + coefficient
    return out


def polynomial_moments(coefficients, y):
    weights = [coefficient * y**m for m, coefficient in enumerate(coefficients)]
    total = sum(weights)
    mean = sum(m * w for m, w in enumerate(weights)) / total
    second = sum(m * m * w for m, w in enumerate(weights)) / total
    return total, mean, second - mean * mean


def randomized_ratio(b, counts, coefficients, u):
    """Exact finite polynomial expectation, using its moment recurrence."""
    v = u / (1 - u)
    mu = 2 + (b - 1) * u
    moments = [u * 0 + 1, v * mu]
    for m in range(1, len(coefficients) - 1):
        moments.append(v * ((2 - u) * m + mu) * moments[-1]
                       - v * v * (1 - u) * m * (m + 1) * moments[-2])
    return (1 - u)**sum(counts) * sum(
        coefficient * moments[m] for m, coefficient in enumerate(coefficients))


def positive_randomized_ratio(b, counts, coefficients, u):
    """Independent all-positive moment formula, for small exact checks."""
    v = u / (1 - u)
    total = u * 0
    for m, coefficient in enumerate(coefficients):
        moment = factorial(m) * sum(
            comb(b - 1, j) * u**j * comb(m + 1, j + 1)
            for j in range(min(m, b - 1) + 1))
        total += coefficient * v**m * moment
    return (1 - u)**sum(counts) * total


def exact_identity_checks():
    comparisons = 0
    for k in (2, 3, 4):
        for n in range(k, 9):
            polynomials = enumerate_polynomials(n, k)
            for counts, poly in polynomials.items():
                if min(counts) == 0:
                    continue
                b, rare = counts[0], counts[1:]
                coefficients = rare_coefficients(rare)
                for u in (Fraction(1, 7), Fraction(1, 3), Fraction(2, 3)):
                    actual = randomized_ratio(b, rare, coefficients, u)
                    positive = positive_randomized_ratio(b, rare, coefficients, u)
                    assert actual == positive == evaluate(poly, u)
                    comparisons += 1
    return comparisons


def concavity_checks():
    comparisons = 0
    for a in range(1, 51):
        coefficients = rare_coefficients((a,))
        for y in (Fraction(1, 100), Fraction(1, 10), Fraction(1), Fraction(3)):
            _, mean, variance = polynomial_moments(coefficients, y)
            assert 0 <= variance <= mean - 1
            assert a * y == mean * mean + variance + (y - 1) * mean
            comparisons += 1
    return comparisons


def hroot(coefficients, A):
    low = Decimal(1) / (A + 1)
    high = low * 2
    while high < 1 and polynomial(coefficients, high) < 1:
        high *= 2
    high = min(high, Decimal(1))
    for _ in range(180):
        middle = (low + high) / 2
        if polynomial(coefficients, middle) < 1:
            low = middle
        else:
            high = middle
    return (low + high) / 2


def crossing(b, counts, coefficients, u0):
    low, high = u0 / 4, u0 * 4
    while randomized_ratio(b, counts, coefficients, low) > 1:
        low /= 2
    while randomized_ratio(b, counts, coefficients, high) < 1:
        high *= 2
        assert high < 1
    for _ in range(130):
        middle = (low + high) / 2
        if randomized_ratio(b, counts, coefficients, middle) < 1:
            low = middle
        else:
            high = middle
    return (low + high) / 2


def tangent_bounds(b, counts, coefficients, u):
    A = sum(counts)
    y = b * u * u
    h, kappa, _ = polynomial_moments(coefficients, y)
    s = kappa / (b * u * (1 - u))
    assert s < 1
    actual = randomized_ratio(b, counts, coefficients, u)
    lower = (1 - u)**A * h
    upper = ((1 - u)**A * h * (-kappa).exp() / (1 - s)**2
             * (1 + u * s / (1 - s))**(b - 1))
    tolerance = Decimal("1e-70") * max(Decimal(1), actual)
    assert lower <= actual + tolerance <= upper + 2 * tolerance
    return lower, actual, upper


def finite_root_checks():
    rows = []
    for rare in ((1,), (1, 1), (2, 7), (2, 5, 9), (30, 30),
                 (1, 100), (100, 200), (2, 50, 500)):
        A, ell = sum(rare), len(rare)
        coefficients = rare_coefficients(rare, Decimal)
        ya = hroot(coefficients, A)
        for scale in (100_000, 1_000_000):
            b = (A + 1) * scale
            u0 = (ya / b).sqrt()
            epsilon = (Decimal(A + 1) / b).sqrt()
            K = ell + Decimal(ell).sqrt() + 1
            delta = 16 * K * epsilon
            assert delta < Decimal("0.5")
            lo = randomized_ratio(b, rare, coefficients, (1 - delta) * u0)
            hi = randomized_ratio(b, rare, coefficients, (1 + delta) * u0)
            assert lo < 1 < hi
            exact = crossing(b, rare, coefficients, u0)
            relative = exact / u0 - 1
            assert abs(relative) <= delta
            for multiplier in (Decimal("0.7"), Decimal(1), Decimal("1.3")):
                tangent_bounds(b, rare, coefficients, multiplier * u0)
            rows.append({"b": b, "rare_counts": rare,
                         "polynomial_root_y": str(ya),
                         "crossing_odds": str(exact),
                         "relative_root_error": str(relative),
                         "error_divided_by_sqrt_mass_ratio": str(relative / epsilon),
                         "proved_relative_error_bound": str(delta)})
    return rows


def divergent_probability_examples():
    rows = []
    for exponent in (6, 12, 24, 48):
        b = 10**exponent
        a = int(Decimal(b) / Decimal(b).ln())
        rare = (a, a)
        results = []
        for cutoff in (300, 380):
            coefficients = rare_coefficients(rare, Decimal, cutoff)
            # H=B_a^2 has the same root as B_a, retaining all positive terms
            # through the selected total degree.
            ya = hroot(coefficients, 2 * a)
            u0 = (ya / b).sqrt()
            value = randomized_ratio(b, rare, coefficients, u0)
            exact = crossing(b, rare, coefficients, u0)
            results.append((ya, value, exact / u0))
        for x, y in zip(*results):
            assert abs(x / y - 1) < Decimal("1e-30")
        ya, value, root_ratio = results[-1]
        assert value > 1
        rows.append({"b": str(b), "a": str(a), "cutoffs": [300, 380],
                     "polynomial_root_y": str(ya),
                     "probability_ratio_at_polynomial_root": str(value),
                     "exact_root_divided_by_polynomial_prediction": str(root_ratio)})
    assert all(x["probability_ratio_at_polynomial_root"] != "1" for x in rows)
    assert all(Decimal(x["probability_ratio_at_polynomial_root"])
               < Decimal(y["probability_ratio_at_polynomial_root"])
               for x, y in zip(rows, rows[1:]))
    return rows


def main():
    exact = exact_identity_checks()
    concavity = concavity_checks()
    with localcontext() as context:
        context.prec = 100
        roots = finite_root_checks()
        divergent = divergent_probability_examples()
    result = {
        "exact_word_and_two_moment_formula_comparisons": exact,
        "rational_concavity_and_differential_equation_checks": concavity,
        "finite_uniform_root_brackets": roots,
        "divergent_probability_examples": divergent,
        "scope": "Numerical checks supplement the written proof; Decimal examples are not interval certificates.",
    }
    destination = Path(__file__).with_name("data") / "vertex-completion-verification.json"
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {exact} exact identity comparisons; {concavity} rational concavity checks; "
          f"{len(roots)} uniform root brackets; {len(divergent)} divergent-probability examples.")
    for row in divergent:
        print(f"b={row['b']}: S(u0)={Decimal(row['probability_ratio_at_polynomial_root']):.8g}, "
              f"u_exact/u0={Decimal(row['exact_root_divided_by_polynomial_prediction']):.8g}")


if __name__ == "__main__":
    main()
