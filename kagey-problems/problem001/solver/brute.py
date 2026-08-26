r"""Exhaustive oracle for problem 001.

For tiny grids: test every blackout S by computing all presentations C(R) \ S,
hashing them, and checking for collisions (injectivity). ~30 lines.
Must agree with engine.py on every grid up to 2x4 and on 3x3.

CODE AUTHOR: Arjun Pemmasani; logic per the
project spec (PROBLEM.md); line-by-line review and acceptance: Arjun and Claude.

Deliberately independent of everything else in three ways:
1. No reduction: validity is checked straight from the definition, injectivity of the
   presentation map. Difference sets, Lemma 1, and pruning appear nowhere.
2. Third enumeration method: rectangles found by testing every 4-subset of points
   (a 4-set is a rectangle iff some pairing into two "diagonals" has equal midpoints
   and equal lengths: bisecting diagonals give a parallelogram, equal ones make it
   a rectangle). No constructive generation shared with oracle_claude.py.
3. No imports from solver/ or reconcile/.

Slow on purpose. Feasible through ~4x4 (2^16 blackouts); 4x5 is minutes.
"""
import time
from itertools import combinations

def grid_points(rows, cols):
    return [(i, j) for i in range(1, cols + 1) for j in range(1, rows + 1)]

def is_rectangle(p, q, r, s):
    for (a, b), (c, d) in (((p, q), (r, s)), ((p, r), (q, s)), ((p, s), (q, r))):
        if (a[0] + b[0], a[1] + b[1]) == (c[0] + d[0], c[1] + d[1]):  # same midpoint*2
            if (a[0]-b[0])**2 + (a[1]-b[1])**2 == (c[0]-d[0])**2 + (c[1]-d[1])**2:
                return True
    return False

def rectangle_masks(rows, cols):
    pts = grid_points(rows, cols)
    idx = {p: k for k, p in enumerate(pts)}
    masks = []
    for quad in combinations(pts, 4):
        if is_rectangle(*quad):
            masks.append(sum(1 << idx[p] for p in quad))
    return masks, len(pts)

def valid(S, rect_masks):
    seen = set()
    for c in rect_masks:
        pres = c & ~S
        if pres in seen:          # includes two fully hidden rectangles: both present 0
            return False
        seen.add(pres)
    return True

def max_blackout_brute(rows, cols):
    """Returns (max blackout size, number of maximum blackouts, number of rectangles).

    Searches blackout sizes from N downward; the first size admitting a valid S is the
    maximum, and every valid S of that size is counted. Exhaustive at each size, so the
    count is exact; sizes below the maximum are never visited.
    """
    rect_masks, N = rectangle_masks(rows, cols)
    if len(rect_masks) < 2:
        return N, 1, len(rect_masks)
    for k in range(N, -1, -1):
        count = 0
        for blk in combinations(range(N), k):
            S = 0
            for b in blk:
                S |= 1 << b
            if valid(S, rect_masks):
                count += 1
        if count:
            return k, count, len(rect_masks)
    raise AssertionError("unreachable: S = empty set is always valid")

if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1:
        grids = [tuple(int(x) for x in a.lower().split("x")) for a in sys.argv[1:]]
    else:
        grids = [(2, 2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4)]
    print("| grid (rows x cols) | rectangles | max blackout | # maximum blackouts | time |")
    print("|---|---|---|---|---|")
    for rows, cols in grids:
        t0 = time.time()
        v, w, nr = max_blackout_brute(rows, cols)
        print(f"| {rows} x {cols} | {nr} | {v} | {w} | {time.time()-t0:.2f}s |", flush=True)
