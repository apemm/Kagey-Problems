"""Difference-set table + preprocessing. OWNER: Arjun.

difference_table(rects) -> list[frozenset]
    All pairwise symmetric differences C1 ^ C2 of corner sets, one per unordered pair.
    By Lemma 1 (PROBLEM.md convention 4) S is valid iff the kept set V \ S meets every row.

prune(rows) -> list[frozenset]
    Deduplicate; delete any row that contains another row (convention 5). A superset row
    is hit whenever its subset is, so it imposes no additional constraint.

Fixture: the pruned 2x4 table must be exactly the six column-pair rows (ledger.md).
"""
from itertools import combinations


def difference_table(rects):
    return [a ^ b for a, b in combinations(rects, 2)]


def prune(rows):
    rows = set(rows)
    if frozenset() in rows:
        # An empty difference set means two identical rectangles; no K can hit it.
        raise ValueError("empty difference set: rectangle list is not deduplicated")
    by_size = sorted(rows, key=len)
    kept = []
    for r in by_size:
        # Only shorter-or-equal rows already kept can be proper subsets of r.
        if not any(k < r for k in kept):
            kept.append(r)
    return sorted(kept, key=lambda r: (len(r), sorted(r)))
