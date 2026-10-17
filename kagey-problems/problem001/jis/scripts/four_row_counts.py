"""Exact counts a_4(m) of maximum blackouts of the 4 x m grid, m >= 6.

Dynamic programme over the product of the register of used double letters (a
subset of the four edges of the row partition) with the exported geometry machine,
for each of the three row partitions.  v[U][s] is the number of words of the
current length that end in geometry state s having used exactly the doubles in U.
A word of length n is counted when U is the full set; those counts are 0 for
n <= 5 and are the maximum blackouts for n >= 6 (the archive's Theorem M).

Usage: python four_row_counts.py [max_width]   (default 600)
Writes jis/data/four_row_counts.json with a_4(m) and the per-partition counts.
"""
import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from four_row_machines import load_all, partition_rows_one_based  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "data")


def partition_counts(machine, max_width):
    """Return [c(0), ..., c(max_width)] for one partition."""
    trans = machine["transitions"]
    n = machine["state_count"]
    edge_bit = {}  # letter index -> register bit
    for k in range(4, 8):
        edge_bit[k] = 1 << (k - 4)
    # sparse vectors: dict (U, s) -> count
    cur = {(0, 0): 1}
    counts = [0]
    for width in range(1, max_width + 1):
        nxt = {}
        for (U, s), c in cur.items():
            row = trans[s]
            for k in range(8):
                t = row[k]
                if t < 0:
                    continue
                if k >= 4:
                    b = edge_bit[k]
                    if U & b:
                        continue
                    key = (U | b, t)
                else:
                    key = (U, t)
                nxt[key] = nxt.get(key, 0) + c
        cur = nxt
        counts.append(sum(c for (U, s), c in cur.items() if U == 15))
    return counts


def main():
    max_width = int(sys.argv[1]) if len(sys.argv) > 1 else 600
    t0 = time.time()
    machines = load_all()
    per = {}
    for name, m in machines:
        t1 = time.time()
        per[name] = partition_counts(m, max_width)
        print(f"partition {name}: states {m['state_count']}, "
              f"{time.time() - t1:.1f} s", flush=True)
    total = [sum(per[name][w] for name in per) for w in range(max_width + 1)]
    # reproduce the archive's anchor values
    assert [per[n][6] for n in per] == [0, 20, 6], [per[n][6] for n in per]
    assert [per[n][7] for n in per] == [4, 256, 32], [per[n][7] for n in per]
    assert total[6] == 26 and total[7] == 292
    assert all(total[w] == 0 for w in range(6))
    print("a_4(6..12) =", total[6:13])
    out = {
        "description": "a_4(m) = number of maximum blackouts of the 4 x m grid "
                       "(m >= 6; entries for m <= 5 are the zero counts of the "
                       "equality family, not optimum counts)",
        "method": "exact integer dynamic programme over (used-double register, "
                  "geometry state) on the three exported machines",
        "machines": {name: m["file"] for name, m in machines},
        "partitions_zero_based_rows": list(per),
        "partitions_one_based_rows": {n: partition_rows_one_based(n) for n in per},
        "max_width": max_width,
        "a4": {str(w): str(total[w]) for w in range(max_width + 1)},
        "per_partition": {n: {str(w): str(per[n][w]) for w in range(max_width + 1)}
                          for n in per},
        "seconds": round(time.time() - t0, 2),
    }
    os.makedirs(DATA, exist_ok=True)
    with open(os.path.join(DATA, "four_row_counts.json"), "w") as f:
        json.dump(out, f, indent=1)
    print(f"wrote four_row_counts.json in {time.time() - t0:.1f} s")


if __name__ == "__main__":
    main()
