"""Exact finite-field checks for the repaired period-49 filler profile."""

from itertools import product
from pathlib import Path
import json


def chi(n):
    n %= 7
    return 0 if n == 0 else (1 if n in (1, 2, 4) else -1)


def main():
    counts = {"binary_transversality": 0, "crossed_filler_pairs": 0,
              "four_filler_pairings": 0, "horizontal_norm_tests": 0,
              "paley_angle_tests": 0}
    for g in range(1, 7):
        kappa = 6 if chi(g) == 1 else 1
        coefficient = (1 + 4 * kappa * kappa) % 7
        assert chi(kappa * g) == -1 and chi(coefficient) == -1
        binary = [(x, 0) for x in (3, 5, 6)] + [(x, g) for x in (0, 1, 2, 4)]
        for x, s in binary:
            y = (s - 3 * g) % 7
            assert (x + 2 * kappa * y) % 7 != 0
            counts["binary_transversality"] += 1
            for d, t in product(range(7), repeat=2):
                v = 2 * kappa * d
                if (x * (t - d) - y * v) % 7 == 0 and (x * (t + d) + y * v) % 7 == 0:
                    assert d == 0
                counts["crossed_filler_pairs"] += 1

        # Side phases a,b and diagonal phases c,d lie on the same
        # nonisotropic line. Any solution has matching unordered phase
        # pairs, or both pairs are constant internally.
        for a, b, c, d in product(range(7), repeat=4):
            norm_test = coefficient * ((b - a) ** 2 - (d - c) ** 2)
            perpendicular = coefficient * (b - a) * (c + d - a - b)
            if norm_test % 7 == 0 and perpendicular % 7 == 0:
                assert sorted((a, b)) == sorted((c, d)) or (a == b and c == d)
            counts["four_filler_pairings"] += 1

        for length, gap in product(range(7), repeat=2):
            if (length * length - coefficient * gap * gap) % 7 == 0:
                assert length == gap == 0
            counts["horizontal_norm_tests"] += 1

        for a_lift in range(1, 7):
            sign_e = chi(5 * g * a_lift)
            phase_e = 0 if sign_e == 1 else 1
            for sign_f, sea_offset in product((-1, 1), (3, 5, 6)):
                phase_f = 0 if sign_f == 1 else 1
                assert ((phase_f - phase_e) * sea_offset - 5 * g * a_lift) % 7 != 0
                counts["paley_angle_tests"] += 1

    # The rejected weaker choice kappa=3 genuinely has a square coarse
    # norm. Preserve its exact local certificate to guard the hypothesis.
    filler, high = 1001, 20000
    side = ((-7, high), (63, high))
    diagonal = ((0, filler), (56, filler + 42))
    white = ((-7, filler + 21), (63, filler + 21))
    sq = lambda pair: sum((pair[1][i] - pair[0][i]) ** 2 for i in (0, 1))
    assert sq(side) == sq(diagonal) == sq(white) == 4900
    assert tuple(sum(p[i] for p in diagonal) for i in (0, 1)) == tuple(sum(p[i] for p in white) for i in (0, 1))

    # This remaining two-label/two-low-sea mixed support satisfies both
    # insertion phases and the valuation filter. A common-corner color
    # can never repair a symmetric-difference certificate.
    a, b, c, d = (7, 421), (367, 1), (350, 505), (122, 1)
    remaining_white = ((416, 43), (56, 463))
    assert sq((a, b)) == sq((c, d)) == sq(remaining_white) == 306000
    assert tuple(c[i] + d[i] for i in (0, 1)) == tuple(sum(p[i] for p in remaining_white) for i in (0, 1))
    assert sum((b[i] - a[i]) * (c[i] + d[i] - a[i] - b[i]) for i in (0, 1)) == 0
    for x, y in (a, c):
        assert x // 7 % 7 == 1
        assert (y - 1) % 7 == 0 and (y - 1) % 49 != 0
        assert chi(5 * ((y - 1) // 7)) == -1
    assert chi(b[0]) == chi(d[0]) == chi(remaining_white[0][0]) == -1

    result = {"status": "PASS", **counts,
              "rejected_kappa_three_certificate_norm": 4900,
              "remaining_low_sea_mixed_certificate_norm": 306000}
    Path(__file__).with_name("seven_phase_filler_checks.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
