"""Check the one-sided mixed-support family disproving the stronger codegree."""
import json
from pathlib import Path


def main():
    results = []
    for h in (9, 17, 33, 65, 129):
        fixed_c, fixed_d = (2, 1), (8, 9)
        white = {(0, 5), (10, 5)}
        assert fixed_c[0] + fixed_d[0] == 10
        assert fixed_c[1] + fixed_d[1] == 10
        assert (fixed_d[0] - fixed_c[0]) ** 2 + (fixed_d[1] - fixed_c[1]) ** 2 == 100
        seen = set()
        for c in range(1, h + 1, 2):
            if c == 5:
                continue
            free, third_pin = (10, c), (0, c)
            tilted = white | {fixed_c, fixed_d}
            axis = white | {free, third_pin}
            support = frozenset({fixed_c, fixed_d, free, third_pin})
            assert len(tilted) == len(axis) == len(support) == 4
            assert tilted ^ axis == support
            assert all(1 <= y <= h and y % 2 for x, y in support)
            assert len({x for x, y in support}) == 4
            assert all(x < 10 for x, y in (fixed_c, fixed_d, third_pin))
            assert support not in seen
            seen.add(support)
        assert len(seen) == (h + 1) // 2 - 1
        results.append({"height": h, "supports": len(seen)})
    result = {"status": "PASS", "fixed_cells": [[2, 1], [8, 9]],
              "free_column": 10, "checks": results}
    Path(__file__).with_name("deleted_letter_codegree_counterexample_check.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
