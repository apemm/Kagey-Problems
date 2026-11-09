"""Exact arithmetic checks for the conic reduction; not an asymptotic proof."""
from pathlib import Path
import json


def main():
    identities = 0
    admissible_discriminants = 0
    matching_identities = 0
    matching_discriminants = 0
    degenerate = []
    for delta in (-1, 0, 1):
        for g in range(1, 52, 2):
            for Y in range(1, 21):
                for T in range(1, 21):
                    y = g * Y
                    A = g * g - 4 * T * T
                    B = 4 * T * (2 * delta - y)
                    C = 4 * delta * y - 4 * delta * delta
                    N = B * B - 4 * A * C
                    assert A != 0
                    assert N == 16 * g * g * (
                        T * T * Y * Y - delta * g * Y + delta * delta
                    )
                    for X in (1, 2, 7, 19):
                        x, gap = g * X, X * T
                        original = x * x - 4 * (gap - delta) * (y + gap - delta)
                        assert original == A * X * X + B * X + C
                        identities += 1
                    if N == 0:
                        assert delta == 1 and Y == 1 and g == T * T + 1
                        degenerate.append([g, Y, T, delta])
                    if delta != 1 or y % 8 == 7:
                        assert N != 0
                        admissible_discriminants += 1
                    A2 = g * g - T * T
                    B2 = 2 * T * (delta - y)
                    C2 = 2 * delta * y - delta * delta
                    N2 = B2 * B2 - 4 * A2 * C2
                    assert N2 == 4 * g * g * (
                        T * T * Y * Y - 2 * delta * g * Y + delta * delta
                    )
                    for X in (1, 2, 7, 19):
                        x, gap = g * X, X * T - delta
                        original = x * x + y * y - (y + gap) ** 2
                        assert original == A2 * X * X + B2 * X + C2
                        matching_identities += 1
                    if y % 4 == 3:
                        assert N2 != 0
                        matching_discriminants += 1
    result = {
        "status": "passed",
        "expanded_equation_checks": identities,
        "nonzero_discriminant_checks": admissible_discriminants,
        "matching_expanded_equation_checks": matching_identities,
        "matching_nonzero_discriminant_checks": matching_discriminants,
        "unrestricted_degenerate_examples": degenerate,
        "scope": "Exact finite algebra checks. The counting bound is proved in the note.",
    }
    path = Path(__file__).with_suffix(".json")
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
