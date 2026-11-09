"""Independent finite checks for insertion_adjacent_component.md.

The checker tests the full virtual parity pair set, even on words with no doubles.
It has no third-party dependencies.
"""

from functools import lru_cache
from itertools import combinations, product
import json


@lru_cache(None)
def placements(h, n):
    out = []
    for b in range(1, h):
        for d in range(1, h - b):
            for a in range(1, b * d + 1):
                if b * d % a:
                    continue
                c = b * d // a
                if a + c >= n:
                    continue
                for r in range(b + 1, h - d + 1):
                    for x in range(n - a - c):
                        out.append(((x, r), (x + a, r - b),
                                    (x + c, r + d), (x + a + c, r - b + d)))
    return out


def violations(h, columns, stop=False, pair_set=None):
    columns = [frozenset((c,)) if isinstance(c, int) else frozenset(c)
               for c in columns]
    seen = {}
    bad = []
    for corners in placements(h, len(columns)):
        white = tuple(sorted((x, r) for x, r in corners if r not in columns[x]))
        if len(white) > 2:
            continue
        if not white:
            bad.append(("hidden", corners))
        elif white in seen:
            bad.append(("collision", corners, seen[white], white))
        else:
            seen[white] = corners
        if white:
            if len(white) == 1:
                x, r = white[0]
                rival = any(((s - r) % 2 if pair_set is None
                             else frozenset((r, s)) in pair_set)
                            for s in columns[x])
            else:
                (x, r), (z, s) = white
                if x == z:
                    rival = ((r - s) % 2 if pair_set is None
                             else frozenset((r, s)) in pair_set)
                elif r == s:
                    rival = bool(columns[x] & columns[z])
                else:
                    rival = s in columns[x] and r in columns[z]
            if rival:
                bad.append(("rival", corners, white))
        if stop and bad:
            return bad
    return bad


def main():
    adjacent = 0
    for h in range(3, 7):
        for r in range(1, h):
            for word in product((r, r + 1), repeat=8):
                assert not violations(h, word, True), (h, word)
                adjacent += 1
    inserted = 0
    for h in range(3, 8):
        memory = 2 * (1 + (h - 1) ** 2 // 4)
        for a in range(1, h + 1):
            for b in range(a + 1, h + 1):
                if (a - b) % 2:
                    word = [1] * memory + [{a, b}] + [h] * memory
                    assert not violations(h, word, True), (h, a, b)
                    inserted += 1
    word = [1, 15, 1, 1, 1, 1, 1, 11]
    assert not violations(15, word)
    padded = violations(15, [1] * 6 + word)
    assert len(padded) == 1 and padded[0][0] == "collision"
    dead_end = [1] * 42 + [5] * 5 + [1] * 4 + [10, 2, 1, 4]
    assert not violations(10, dead_end)
    dead_state = dead_end[-42:]
    assert all(violations(10, dead_state + [a], True) for a in range(1, 11))
    general_inserted = general_switches = even_boundary = 0
    for h in range(3, 8):
        memory = 2 * (1 + (h - 1) ** 2 // 4)
        for small_part in combinations(range(1, h + 1), h // 2):
            if h % 2 == 0 and 1 not in small_part:
                continue
            part = set(small_part)
            pairs = {frozenset((a, b)) for a in part
                     for b in range(1, h + 1) if b not in part}
            for word in ([1] * memory + [h] * memory,
                         [h] * memory + [1] * memory):
                assert not violations(h, word, True, pairs)
                general_switches += 1
            for edge in pairs:
                word = [1] * memory + [edge] + [h] * memory
                assert not violations(h, word, True, pairs)
                general_inserted += 1
            if h % 2 == 0:
                for word in product((1, h), repeat=8):
                    assert not violations(h, word, True, pairs)
                    even_boundary += 1
    print(json.dumps({"adjacent_words_checked": adjacent,
                      "isolated_doubles_checked": inserted,
                      "padding_counterexample": padded,
                      "dead_end_height": 10,
                      "dead_end_reachable_prefix_length": len(dead_end),
                      "dead_end_outdegree": 0,
                      "all_partition_switches_checked": general_switches,
                      "all_partition_doubles_checked": general_inserted,
                      "even_height_boundary_words_checked": even_boundary}, indent=2))


if __name__ == "__main__":
    main()
