"""Direct enumeration of the four-row maximum blackouts, independent of the machines.

A maximum blackout of the 4 x m grid (m >= 6) has m+4 points: four double columns
whose row pairs are the four edges of a balanced partition of the rows into two
pairs, each edge used once, and one black point in every other column (the
equality lemma of the four-row theorem).  This script lists those candidates and
tests each one against every rectangle with verify_narrow.rectangles and
verify_narrow.collision, the repository's own equal-diagonal enumerator.

Two modes:
  flat W     every candidate of width W is built and tested whole, no pruning;
  dfs  W...  column-by-column search; a prefix is abandoned as soon as two
             rectangles lying inside the columns read so far have the same
             presentation, because that collision persists in every extension.

Coordinates in the output are one-based (column, row), (1,1) top left, exactly as
in verify_narrow.py, bit (row-1)*m + (column-1).  Internally columns and rows are
zero-based.  Each width stops after TIME_CAP seconds and is then reported as
unresolved.
"""
import json
import os
import sys
import time
from itertools import combinations, permutations, product

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", ".."))
import verify_narrow  # noqa: E402

DATA = os.path.join(HERE, "..", "data")
TIME_CAP = 1800.0  # seconds per width

PARTITIONS = [("01|23", ((0, 1), (2, 3))), ("02|13", ((0, 2), (1, 3))),
              ("03|12", ((0, 3), (1, 2)))]


def edges_of(part):
    left, right = part
    return [frozenset((a, b)) for a in left for b in right]


def mask_of(columns, m):
    """columns[x] = black rows in column x -> bitmask with bit y*m+x."""
    return sum(1 << (y * m + x) for x, rows in enumerate(columns) for y in rows)


def points_one_based(columns):
    return [[x + 1, y + 1] for x, rows in enumerate(columns) for y in sorted(rows)]


def flat(m):
    rects = verify_narrow.rectangles(4, m)
    t0 = time.time()
    result = {"width": m, "mode": "flat", "rectangles": len(rects),
              "candidates": 3 * m * (m - 1) * (m - 2) * (m - 3) * 4 ** (m - 4)}
    counts = {}
    witnesses = {}
    tested = 0
    for name, part in PARTITIONS:
        edges = edges_of(part)
        cnt = 0
        for dcols in combinations(range(m), 4):
            scols = [x for x in range(m) if x not in dcols]
            for order in permutations(edges):
                base = [None] * m
                for x, e in zip(dcols, order):
                    base[x] = tuple(sorted(e))
                for rows in product(range(4), repeat=len(scols)):
                    cols = list(base)
                    for x, r in zip(scols, rows):
                        cols[x] = (r,)
                    black = mask_of(cols, m)
                    tested += 1
                    if verify_narrow.collision(rects, black) is None:
                        cnt += 1
                        if name not in witnesses:
                            witnesses[name] = points_one_based(cols)
                if time.time() - t0 > TIME_CAP:
                    result.update(status="unresolved", tested=tested,
                                  seconds=round(time.time() - t0, 1))
                    return result
        counts[name] = cnt
        print(f"flat width {m} partition {name}: {cnt} valid, "
              f"{time.time() - t0:.0f} s", flush=True)
    assert tested == result["candidates"]
    result.update(status="done", tested=tested, per_partition=counts,
                  total=sum(counts.values()), first_witness_per_partition=witnesses,
                  seconds=round(time.time() - t0, 1))
    return result


def dfs(m):
    rects = verify_narrow.rectangles(4, m)
    by_last = [[] for _ in range(m)]
    for r in rects:
        last = max(i % m for i in range(4 * m) if r >> i & 1)
        by_last[last].append(r)
    t0 = time.time()
    result = {"width": m, "mode": "dfs", "rectangles": len(rects),
              "candidates": 3 * m * (m - 1) * (m - 2) * (m - 3) * 4 ** (m - 4)}
    counts = {}
    witnesses = {}
    nodes = 0
    for name, part in PARTITIONS:
        edges = edges_of(part)
        letters = [(r,) for r in range(4)] + [tuple(sorted(e)) for e in edges]
        seen = {}
        cols = []
        cnt = 0
        timed_out = False

        def extend(x, black, unused, used_mask):
            nonlocal cnt, nodes, timed_out
            if timed_out:
                return
            if x == m:
                if unused == 0:
                    cnt += 1
                    if name not in witnesses:
                        witnesses[name] = points_one_based(cols)
                return
            if unused > m - x:
                return
            nodes += 1
            if nodes % 100000 == 0 and time.time() - t0 > TIME_CAP:
                timed_out = True
                return
            for k, rows in enumerate(letters):
                if k >= 4:
                    bit = 1 << (k - 4)
                    if used_mask & bit:
                        continue
                    new_unused, new_used = unused - 1, used_mask | bit
                else:
                    new_unused, new_used = unused, used_mask
                nb = black
                for y in rows:
                    nb |= 1 << (y * m + x)
                added = []
                ok = True
                for r in by_last[x]:
                    vis = r & ~nb
                    if vis in seen:
                        ok = False
                        break
                    seen[vis] = r
                    added.append(vis)
                if ok:
                    cols.append(rows)
                    extend(x + 1, nb, new_unused, new_used)
                    cols.pop()
                for vis in added:
                    del seen[vis]

        extend(0, 0, 4, 0)
        if timed_out:
            result.update(status="unresolved", nodes=nodes,
                          seconds=round(time.time() - t0, 1))
            return result
        counts[name] = cnt
        print(f"dfs width {m} partition {name}: {cnt} valid, nodes {nodes}, "
              f"{time.time() - t0:.0f} s", flush=True)
    result.update(status="done", nodes=nodes, per_partition=counts,
                  total=sum(counts.values()), first_witness_per_partition=witnesses,
                  seconds=round(time.time() - t0, 1))
    return result


def main():
    mode = sys.argv[1]
    widths = [int(w) for w in sys.argv[2:]]
    results = []
    for m in widths:
        res = flat(m) if mode == "flat" else dfs(m)
        if "first_witness_per_partition" in res:
            for name, pts in res["first_witness_per_partition"].items():
                black = verify_narrow.mask([(c - 1, r - 1) for c, r in pts], m)
                assert black.bit_count() == m + 4
                assert verify_narrow.collision(verify_narrow.rectangles(4, m), black) is None
        results.append(res)
        print(json.dumps(res), flush=True)
        os.makedirs(DATA, exist_ok=True)
        with open(os.path.join(DATA, f"four_row_direct_{mode}.json"), "w") as f:
            json.dump({"method": "direct enumeration of equality candidates with "
                                 "verify_narrow.collision", "mode": mode,
                       "coordinates": "one-based (column, row), (1,1) top left",
                       "time_cap_seconds": TIME_CAP, "results": results}, f, indent=1)


if __name__ == "__main__":
    main()
