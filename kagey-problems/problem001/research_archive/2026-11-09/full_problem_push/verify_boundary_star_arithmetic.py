"""Exact integer checks for the two explicit mixed-support families."""
from pathlib import Path
import json


def check(p, D, z, k):
    assert p >= 4 and p % 4 == 0 and D > 0 and z > 0 and k > 0
    assert k * (p * D - 2 * z) == z * z + D * D
    assert z * k % D == 0
    a = z * (p * D + k) // D
    assert a % 2 == 1
    h = a + 2 * D + 1
    i = (a - 1) // 2
    X = p * i
    A, C = (X, a + 1), (X + p * D, h)
    B, E = (X + p * D + k, 1), (X + 2 * z + k, 1)
    W, Z = (B[0] + z, B[1] + D), (A[0] + z, A[1] + D)
    U = (A[0] - B[0], A[1] - B[1])
    V = (C[0] - E[0], C[1] - E[1])
    assert U[0] * z + U[1] * D == 0
    assert sum(t*t for t in U) == sum(t*t for t in V)
    assert tuple(W[j] + Z[j] for j in (0, 1)) == tuple(E[j] + C[j] for j in (0, 1))
    R, T = {A, B, W, Z}, {C, E, W, Z}
    assert len(R) == len(T) == 4 and R != T
    def black(point):
        x, y = point
        return y == 1 or (x % p == 0 and 0 <= x // p < h // 2 and y == 2 * (x // p) + 2)
    assert all(black(Q) for Q in (A, B, C, E))
    assert all(1 <= Q[1] <= h and not black(Q) for Q in (W, Z))
    assert {Q for Q in R if not black(Q)} == {W, Z}
    assert {Q for Q in T if not black(Q)} == {W, Z}
    return dict(p=p, height=h, D=D, z=z, k=k,
                side=[B,A], diagonal=[E,C], common_whites=[W,Z])


if __name__ == "__main__":
    universal = [check(p, (p-2)//2, (p-2)//2, 1) for p in range(4, 257, 4)]
    square = [check((z+1)**2, 1, z, 1) for z in range(1, 64, 2)]
    assert all(case["height"] == case["p"]**2//2 for case in universal)
    result = {"status": "PASS", "universal_cases": universal, "square_cases": square,
              "scope": "Exact mixed-collision certificates, not a full-board search"}
    Path(__file__).with_name("boundary_star_arithmetic_check.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "universal_cases":len(universal),
                      "square_cases":len(square)}))
