"""Replay Paper A's finite certificates with outward error bounds.

Run from any directory. No root search, parameter sweep or external library.
Exact integer run-count and independent DP checks are replayed through N=174.
All 999 stored brackets and the intermediate sign range are checked with
enclosed run-count sums, including a geometric bound on any omitted tail.
Any failed or undecided comparison raises an exception and exits nonzero.
"""
import csv
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import time

from certified_decimal import (
    C0, I, PI, central_sum, certificate_margins, threshold_gap,
    zeta_bounds, zeta_grid,
)
import verify_every_n as legacy

ROOT = Path(__file__).resolve().parent


def verify():
    start = time.monotonic()
    lines = [f"verify_certified_bounds.py  {datetime.now(timezone.utc).isoformat()}",
             "80-digit outward intervals; pi from exact Machin-series bounds"]
    minima = {}

    def positive(name, N, value):
        if value.lo <= 0:
            raise ArithmeticError(f"{name} failed at N={N}: {value}")
        if name not in minima or value.lo < minima[name][1]:
            minima[name] = (N, value.lo)

    with (ROOT / "data/every_n_certificates.csv").open(newline="") as stream:
        rows = list(csv.DictReader(stream))
    if [int(row["N"]) for row in rows] != list(range(2, 1001)):
        raise ValueError("Expected exactly one stored bracket for each N=2..1000")
    for row in rows:
        N = int(row["N"])
        a, b = int(row["u_lo_times_1e9"]), int(row["u_hi_times_1e9"])
        den = 10 ** 9
        if not 0 < a < b:
            raise ValueError(f"Invalid rational endpoints at N={N}")
        if N <= 174:
            coeffs = legacy.runcount_coeffs(N)
            target = den ** (N - 1)
            low = legacy.S_int_runcount2(coeffs, a, den)
            high = legacy.S_int_runcount2(coeffs, b, den)
            if not (low < target < high
                    and low == legacy.S_int_dp(N, a, den)
                    and high == legacy.S_int_dp(N, b, den)):
                raise ArithmeticError(f"Exact certificate failed at N={N}")
        positive("S_lo", N, 1 - central_sum(N, I.rational(a, den)))
        positive("S_hi", N, central_sum(N, I.rational(b, den)) - 1)
        for name, margin in certificate_margins(N, a, b).items():
            positive(name, N, margin)
            if N <= 174 and name in ("upper", "lower", "R_upper", "R_lower"):
                positive("short_" + name, N, margin)
    lines.append("PASS: exact run-count = independent integer DP at both endpoints, N=2..174")
    lines.append("PASS: all 999 rational root brackets, every-N bounds, crossing-equation")
    lines.append("      remainders, log bounds, nu bounds and sign pattern, N=2..1000")

    for N in range(1001, 2774):
        a, uz = zeta_grid(N, 10 ** 7)
        v = I.rational(a + 1, 10 ** 7)
        positive("sign_grid", N, v - uz)
        positive("intermediate_sign", N, 1 - central_sum(N, v))
    lines.append("PASS: z_N > zeta_N for all 1773 integers N=1001..2773")
    for N in (15, 16, 218, 219):
        a, uz = zeta_grid(N, 10 ** 30)
        positive("fine_grid_left", N, uz - I.rational(a, 10 ** 30))
        positive("fine_grid_right", N, I.rational(a + 1, 10 ** 30) - uz)
    lines.append("PASS: rational grid separation at N=15,16,218,219")
    positive("threshold_below", 2773, -threshold_gap(2773))
    positive("threshold_above", 2774, threshold_gap(2774))
    positive("zeta_below_four", 174, 4 - zeta_bounds(174))
    positive("zeta_above_four", 175, zeta_bounds(175) - 4)
    positive("nu_two", 2, I(2).ln() - I(2).ln().ln() / 2 + C0 - I("0.40"))
    positive("log_two", 2, I(2).ln() - I.rational(2, 3))
    positive("exp_two", 2, 8 - I(2).exp())
    # Rounded constants corrected in Appendix A, evaluated at zeta=4.
    n4 = ((I(32) / PI).ln() / 2).exp() * I(4).exp()
    positive("appendix_epsilon", 4, I("0.114777") - 20 / n4)
    tau = I.rational(1, 32) + I.rational(3, 2048) + I.rational(37, 32768) + I.rational(1, 524288)
    B4 = I.rational(5, 128) - I.rational(37, 2048) - I.rational(1, 4096) - I.rational(1, 32768) - 16 * tau ** 2 / (2 * (1 - tau))
    positive("appendix_tau", 4, I("0.033846") - tau)
    positive("appendix_four_tau", 4, I("0.135384") - 4 * tau)
    positive("appendix_B", 4, B4 - I("0.011236"))
    lines.append("PASS: 174/175 split, 2773/2774 threshold and corrected appendix constants")
    lines.append(f"pi enclosure width <= {PI.width():.3E}")
    lines.append("zeta brackets have half-width 1e-45 (plus outward endpoint rounding)")
    lines.append("Strict lower bounds on margins (rounded downward to six significant digits)")
    from decimal import Context, ROUND_FLOOR
    display = Context(prec=6, rounding=ROUND_FLOOR)
    for name, (N, value) in sorted(minima.items()):
        lines.append(f"  {name}: > {display.plus(value)} at N={N}")
    lines.append(f"Elapsed {time.monotonic() - start:.2f}s")
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    result = verify()
    print(result, end="")
    (ROOT / "data/certified_bounds_output.txt").write_text(result, encoding="utf-8")
    inputs = ("certified_decimal.py", "verify_certified_bounds.py", "verify_every_n.py",
              "data/every_n_certificates.csv")
    manifest = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(),
        "all_checks_passed": True,
        "decimal_precision": 80,
        "exact_run_count_and_dp_range": [2, 174],
        "stored_brackets_checked": 999,
        "intermediate_sign_range": [1001, 2773],
        "source_sha256": {
            name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            for name in inputs
        },
        "output_sha256": hashlib.sha256(
            (ROOT / "data/certified_bounds_output.txt").read_bytes()).hexdigest(),
    }
    (ROOT / "data/certified_bounds_manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
