"""Exact certificates for the residual mixed congruence template."""

from math import lcm
from pathlib import Path
import json


def chi(n):
    n %= 7
    return 0 if n == 0 else 1 if n in (1, 2, 4) else -1


def norm(pair):
    return sum((pair[1][i] - pair[0][i]) ** 2 for i in (0, 1))


def main():
    cases = []
    for original_modulus in (1, 2, 3, 5, 7, 11, 49, 98, 105, 343, 1001, 2401):
        modulus = lcm(original_modulus, 49)
        coprime, exponent = modulus, 0
        while coprime % 7 == 0:
            coprime //= 7
            exponent += 1
        K = max(2, exponent)
        T = 7 ** K
        # One exact CRT solution; adding its period preserves all conditions.
        t = (2 * coprime) * pow(2 * coprime, -1, T)
        t += 1000 * 2 * coprime * T
        assert t % (2 * coprime) == 0 and t % T == 1
        s = T + 7
        x = 3 * (s * s + 1)
        a = 7 * x
        c = a + 6 * T
        z = 42 * T + 150
        D = 3 * T * T + 42 * T
        raw = ((0, a), (x, 0), (D, c), (z, 0),
               (3 * T * T + 63 * T + 150, 3 * T), (21 * T, a + 3 * T))
        A, B, C, E, W, Z = tuple((t * px, 1 + t * py) for px, py in raw)
        height = 1000 * T * T * t
        assert norm((A, B)) == norm((C, E)) == norm((W, Z))
        assert tuple(C[i] + E[i] for i in (0, 1)) == tuple(W[i] + Z[i] for i in (0, 1))
        assert sum((B[i] - A[i]) * (C[i] + E[i] - A[i] - B[i]) for i in (0, 1)) == 0
        assert len({A, B, C, E, W, Z}) == 6
        assert all(1 <= point[1] <= height for point in (A, B, C, E, W, Z))
        for point in (A, C):
            assert point[1] % 2 == 1
            assert (point[1] - 1) % 7 == 0 and (point[1] - 1) % 49 != 0
            assert chi(5 * ((point[1] - 1) // 7)) == 1
            assert point[0] % 49 == 0
        assert (C[0] - A[0]) % modulus == 0
        assert (C[1] - A[1]) % modulus == 0
        assert chi(B[0]) == chi(E[0]) == chi(W[0]) == -1
        assert W[1] != 1 and Z[0] % 49 == 0
        cases.append({"modulus": original_modulus, "K": K,
                      "height": height, "squared_norm": norm((A, B))})
    result = {"status": "PASS", "cases": cases}
    Path(__file__).with_name("residual_mixed_congruence_checks.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "PASS", "case_count": len(cases)}))


if __name__ == "__main__":
    main()
