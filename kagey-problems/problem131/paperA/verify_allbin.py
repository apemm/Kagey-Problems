"""Numerical and exact checks for the all-bin threshold theorem.

Standard library only. The Decimal checks are numerical; the proof is in
allbin_thresholds.tex.
Run: python -B verify_allbin.py
"""
from decimal import Decimal, localcontext
from math import comb
from pathlib import Path
import json

D = Decimal
EPS = D("1e-65")


def ratio(a, b, x):
    """Exact run polynomial, numerically evaluated at u=x/sqrt(ab)."""
    u = x / D(a * b).sqrt()
    u2 = u * u
    term = D(1)
    total = D(0)
    for r in range(a):
        add = term * (2 * u + D(a + b - 2 - 2 * r) * u2 / (r + 1))
        total += add
        if r + 1 == a:
            break
        multiplier = D((a - 1 - r) * (b - 1 - r)) * u2 / (r + 1) ** 2
        if r > 4 and multiplier < D("0.5") and abs(add) < EPS * max(total, 1):
            break
        term *= multiplier
    return total


def bessel(x):
    t0, t1 = D(1), x
    i0, i1 = t0, t1
    r = 0
    while True:
        r += 1
        t0 *= x * x / (r * r)
        t1 *= x * x / (r * (r + 1))
        i0 += t0
        i1 += t1
        if r > x + 4 and max(t0, t1) < EPS * max(i0, i1, 1):
            return i0, i1


def bessel_ratio(a, b, x):
    s = D(a * b).sqrt()
    i0, i1 = bessel(x)
    return 2 * x / s * (i0 + D(a + b) / (2 * s) * i1)


def root(f):
    lo, hi = D(0), D(1)
    while f(hi) < 1:
        hi *= 2
    for _ in range(220):
        mid = (lo + hi) / 2
        if f(mid) < 1:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def laguerre_values(a, y):
    term = y
    h, hp, hpp = D(0), D(0), D(0)
    for r in range(a):
        h += term
        hp += (r + 1) * term / y
        hpp += r * (r + 1) * term / (y * y)
        if r + 1 == a:
            break
        multiplier = D(a - 1 - r) * y / ((r + 1) * (r + 2))
        if r > 4 and multiplier < D("0.5") and term < EPS:
            break
        term *= multiplier
    return h, hp, hpp


def coefficients(n, a):
    ans = [0] * n
    b = n - a
    for r in range(a):
        t = comb(a - 1, r) * comb(b - 1, r)
        ans[2 * r + 1] += 2 * t
        if 2 * r + 2 < n:
            ans[2 * r + 2] += (n - 2 - 2 * r) * t // (r + 1)
    return ans


def run():
    stats = {"arithmetic": "Decimal, precision 80; not interval arithmetic"}
    count = 0
    for n in range(4, 151):
        for a in range(1, n // 2):
            c1, c2 = coefficients(n, a), coefficients(n, a + 1)
            assert all(v <= w for v, w in zip(c1, c2))
            assert c1[3] < c2[3]
            count += 1
    stats["exact_inward_coefficient_comparisons"] = count
    count = 0
    for a in [1, 2, 3, 5, 10, 30, 100, 1000, 10**6]:
        for b in sorted({a, a + 1, 2 * a, 10 * a, 10**12}):
            for x in map(D, ["0.01", "0.25", "1", "2", "5", "12"]):
                actual, approx = ratio(a, b, x), bessel_ratio(a, b, x)
                deficit = 1 - actual / approx
                A, s = D(a * b) / (a + b), D(a * b).sqrt()
                bound = x * x / (2 * A) + x / s
                assert deficit >= -D("1e-60")
                assert deficit <= bound + D("1e-60")
                count += 1
    stats["general_bessel_bound_checks"] = count
    samples = []
    for a, b in [(1, 10**6), (2, 10**6), (5, 10**9), (100, 10**12),
                 (10000, 10**20), (10**6, 10**6), (10**6, 10**30)]:
        x = root(lambda v: ratio(a, b, v))
        xb = root(lambda v: bessel_ratio(a, b, v))
        A, s = D(a * b) / (a + b), D(a * b).sqrt()
        delta = x * x / (2 * A) + x / s
        assert x >= xb - D("1e-60")
        if delta < 1:
            assert x - xb <= -(1 - delta).ln() / 2 + D("1e-60")
        samples.append({"a": a, "b": b, "u": str(x / s),
                        "z": str(2 * x), "bessel_z": str(2 * xb),
                        "relative_error_bound": str(delta)})
    stats["root_samples"] = samples
    edges = []
    for a in [1, 2, 3, 5, 10, 30]:
        y = root(lambda v: laguerre_values(a, v)[0])
        c = y.sqrt()
        _, hp, hpp = laguerre_values(a, y)
        gamma = (1 + y + (y + y * y / 2) * hpp / hp) / (2 * c)
        errors = []
        for b in [10**4, 10**6, 10**8]:
            x = root(lambda v: ratio(a, b, v))
            u = x / D(a * b).sqrt()
            prediction = c / D(b).sqrt() - 1 / D(b) + gamma / D(b) ** D("1.5")
            errors.append({"b": b, "u": str(u),
                           "b2_times_third_order_residual": str(D(b) ** 2 * (u - prediction)),
                           "b_times_first_order_residual": str(D(b) * (u - c / D(b).sqrt()))})
        edges.append({"a": a, "y": str(y), "gamma": str(gamma), "samples": errors})
    stats["fixed_edge_expansions"] = edges
    count = 0
    for a in [1, 2, 5, 10, 100, 10000, 10**6]:
        for x in map(D, ["0.1", "1", "3", "10"]):
            h = laguerre_values(a, x * x / a)[0]
            _, i1 = bessel(x)
            deficit = 1 - a * h / (x * i1)
            assert -D("1e-60") <= deficit <= x * x / (2 * a) + D("1e-60")
            count += 1
    stats["laguerre_bessel_bound_checks"] = count
    layers = []
    for exponent in [100, 400]:
        n = 10**exponent
        for gamma in map(D, ["0.6", "0.75", "0.9"]):
            v = D(n) ** (-gamma)
            t = 1 / (D(n).sqrt() * v)
            d = t * t * t.ln() ** 2
            lower, upper = int(d / 2), int(2 * d)
            assert upper < n // 2
            lower_ratio = ratio(lower, n - lower, D(lower * (n - lower)).sqrt() * v)
            upper_ratio = ratio(upper, n - upper, D(upper * (n - upper)).sqrt() * v)
            assert lower_ratio < 1 < upper_ratio
            layers.append({"N_power_of_10": exponent, "gamma": str(gamma),
                           "predicted_layer_width": str(d),
                           "ratio_at_half_prediction": str(lower_ratio),
                           "ratio_at_twice_prediction": str(upper_ratio)})
    stats["moving_boundary_layer_brackets"] = layers
    dest = Path(__file__).with_name("data") / "allbin-verification.json"
    dest.parent.mkdir(exist_ok=True)
    dest.write_text(json.dumps(stats, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in stats.items() if not isinstance(v, list)}, indent=2))
    print(f"Root and expansion data: {dest}")


if __name__ == "__main__":
    with localcontext() as ctx:
        ctx.prec = 80
        run()
