"""Exhaust the modulo-seven mixed roles used in the remaining-cost map."""

from collections import Counter
from itertools import combinations, product
from pathlib import Path
import json


SEA = {
    "L": [(x, 0) for x in (3, 5, 6)],
    "H": [(x, 1) for x in (1, 2, 4)],
    "F": [(0, 3)],
}
PARITY = {"L": 1, "H": 0, "F": 1}


def mixed(a, b, c, d):
    u = (b[0] - a[0], b[1] - a[1])
    v = (d[0] - c[0], d[1] - c[1])
    z = (c[0] + d[0] - a[0] - b[0],
         c[1] + d[1] - a[1] - b[1])
    return ((u[0] ** 2 + u[1] ** 2 - v[0] ** 2 - v[1] ** 2) % 7 == 0
            and (u[0] * z[0] + u[1] * z[1]) % 7 == 0)


def main():
    answer = {"status": "PASS", "scope": "necessary modular conditions only"}
    for block in ("oriented", "zero"):
        counts = Counter()
        cases = 0
        for p, q in product(range(2), repeat=2):
            a = 0 if block == "zero" or p else 5
            b = 0 if block == "zero" or q else 5
            for s, t in ("LL", "HH", "FF", "LF", "FH", "LH"):
                if (p + q + PARITY[s] + PARITY[t]) % 2:
                    continue
                for sea_a, sea_b in product(SEA[s], SEA[t]):
                    points = ((0, a), (0, b), sea_a, sea_b)
                    for side in combinations(range(4), 2):
                        diagonal = tuple(i for i in range(4) if i not in side)
                        cases += 1
                        if not mixed(*(points[i] for i in side + diagonal)):
                            continue
                        role = ("labels-side" if side == (0, 1) else
                                "sea-side" if side == (2, 3) else "cross")
                        counts[(s + t, role, a, b)] += 1
        levels = {key[0] for key in counts}
        assert levels == ({"LL", "HH", "FF", "LH"} if block == "oriented"
                          else {"LL", "HH", "FF"})
        for (levels, role, a, b), count in counts.items():
            if levels == "LH":
                assert role == "cross" and {a, b} == {0, 5} and count == 1
        answer[block] = {
            "cases": cases,
            "survivors": [{"levels": s, "role": r, "label_rows": [a, b],
                           "count": count}
                          for (s, r, a, b), count in sorted(counts.items())],
        }
    output = Path(__file__).with_name("refined_pair_role_table_check.json")
    output.write_text(json.dumps(answer, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "PASS", "cases": sum(answer[b]["cases"]
                      for b in ("oriented", "zero"))}))


if __name__ == "__main__":
    main()
