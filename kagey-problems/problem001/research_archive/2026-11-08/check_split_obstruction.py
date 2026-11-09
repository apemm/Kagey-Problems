"""Finite independent checks for construction_split_obstruction.md.

These checks support the elementary proofs; they do not search for valid boards.
Run with the bundled Python interpreter or any Python 3 interpreter.
"""

import json
from collections import Counter
from math import isqrt


def check_window(cap, rows_per_type=3):
    length = 2 * cap + 1
    labels = range(2 * rows_per_type)
    word = []
    counts = Counter()
    accepted = failures = 0

    def visit():
        nonlocal accepted, failures
        if len(word) == length:
            accepted += 1
            for kind in range(2):
                tracks = {i % 2 for i, row in enumerate(word)
                          if row // rows_per_type == kind}
                if len(tracks) == 2:
                    failures += 1
                    break
            return
        position = len(word)
        for row in labels:
            if counts[row] == cap:
                continue
            if any(i % 2 != position % 2 and row != other
                   and row // rows_per_type == other // rows_per_type
                   for i, other in enumerate(word)):
                continue
            word.append(row)
            counts[row] += 1
            visit()
            counts[row] -= 1
            word.pop()

    visit()
    assert failures == 0
    return dict(cap=cap, length=length, accepted=accepted, failures=failures)


def check_range(max_height=35):
    cases = same_sign = 0
    for h in range(3, max_height + 1):
        bound = (h - 1) ** 2 // 64
        for r in range(1, h + 1):
            for a in range(1 - r, h + 1 - r):
                for b in range(1 - r, h + 1 - r):
                    if not a or not b or not 1 <= r + a + b <= h:
                        continue
                    if (a * b) % 16:
                        continue
                    product = abs(a * b) // 16
                    for u in range(1, isqrt(product) + 1):
                        if product % u:
                            continue
                        v = product // u
                        cases += 1
                        same_sign += (a * b > 0)
                        assert max(u, v) <= bound
    assert same_sign > 0
    return dict(max_height=max_height, factor_cases=cases,
                same_sign_row_difference_cases=same_sign, failures=0)


def main():
    results = {
        "window_lemma": [check_window(cap) for cap in (1, 2, 3)],
        "corrected_range": check_range(),
        "split_threshold": {"k": 65, "R": 65 ** 2 // 16, "needed": 4 * 65},
        "even_threshold": {"k": 33, "R": 33 ** 2 // 16, "needed": 2 * 33 + 2},
    }
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
