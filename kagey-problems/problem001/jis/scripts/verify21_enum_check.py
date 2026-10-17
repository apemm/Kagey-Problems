"""Explicit enumeration of maximum blackouts of the 5 x m grid under the equality structure,
by a depth-first search over column letters that reuses the per-column analysis of the
transfer count (verify21_count_check), and a definitional recheck of every blackout found:
injectivity of the visible-corner map over all rectangles of the right-angle-triple
enumerator, and verify_narrow.collision.

The search runs the row partitions in the order {1,2}, {1,3}, ..., {4,5} and stops at the cap,
so a run with a cap of N that reports N blackouts, each rechecked, is a proof that at least N
labelled optima exist; a run that finishes below the cap is a complete enumeration that can be
compared with the transfer count. Coordinates in the output are one-based (column, row).

Usage: python verify21_enum_check.py WIDTH [--cap 10001] [--minutes 20] [--tag NAME]
"""
import argparse
import json
import os
import sys
import time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.abspath(os.path.join(HERE, '..', '..')))
import verify21_common_check as C  # noqa: E402
import verify21_count_check as K  # noqa: E402
import verify_narrow  # noqa: E402

DATA = os.path.join(HERE, '..', 'data')
H = 5


def enumerate_partition(m, two_rows, W, temps, cap, deadline, found, per_partition):
    other = [r for r in range(H) if r not in two_rows]
    edge_list = [frozenset((a, b)) for a in two_rows for b in other]
    edges = set(edge_list)
    rows_of = [frozenset((r,)) for r in range(H)] + edge_list
    letters = list(range(H + len(edge_list)))
    full = (1 << len(edge_list)) - 1
    low = (1 << H) - 1
    cache = {}

    def analyse(window, letter):
        key = (window, letter)
        if key in cache:
            return cache[key]
        cols = window + (letter,)
        blackset = {(i, y) for i, L in enumerate(cols) if L >= 0 for y in rows_of[L]}
        hidden = 0
        pres = []
        ok = True
        for span, corners in temps:
            if cols[W - span] < 0:
                continue
            vis = frozenset((W - span + dx, y) for dx, y in corners
                            if (W - span + dx, y) not in blackset)
            if len(vis) >= 3:
                continue
            if not vis:
                hidden += 1
                continue
            if K.axis_rival(vis, blackset, edges, H) or vis in pres:
                ok = False
                break
            pres.append(vis)
        result = None
        if ok and hidden <= 1:
            result = (hidden, tuple(sum(1 << ((x - W + W) * H + y) for x, y in v) for v in pres))
        cache[key] = result
        return result

    def dfs(col, window, pending, used, hidden, word):
        if len(found) >= cap or time.time() > deadline:
            return
        if col == m:
            if used == full:
                pts = set()
                for x, L in enumerate(word):
                    for y in rows_of[L]:
                        pts.add((x, y))
                found.append((two_rows, frozenset(pts)))
                per_partition[two_rows] = per_partition.get(two_rows, 0) + 1
            return
        if bin(full ^ used).count('1') > m - col:
            return                      # the unused edges no longer fit in the remaining columns
        shifted = [v >> H for v in pending]
        for letter in letters:
            if letter >= H:
                b = 1 << (letter - H)
                if used & b:
                    continue
                nused = used | b
            else:
                nused = used
            res = analyse(window, letter)
            if res is None:
                continue
            dh, pres = res
            if hidden + dh > 1 or any(v in shifted for v in pres):
                continue
            npending = tuple(v for v in shifted + list(pres) if not v & low)
            dfs(col + 1, window[1:] + (letter,), npending, nused, hidden + dh, word + [letter])

    dfs(0, (-1,) * W, (), 0, 0, [])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('width', type=int)
    ap.add_argument('--cap', type=int, default=10001)
    ap.add_argument('--minutes', type=float, default=20.0)
    ap.add_argument('--tag', default=None)
    a = ap.parse_args()
    m = a.width
    t0 = time.time()
    deadline = t0 + 60 * a.minutes
    W, temps = K.templates(H)
    found = []
    per = {}
    for two in combinations(range(H), 2):
        enumerate_partition(m, two, W, temps, a.cap, deadline, found, per)
        if len(found) >= a.cap or time.time() > deadline:
            break
    search_seconds = time.time() - t0
    rects = C.rectangles(H, m)
    narrow = verify_narrow.rectangles(H, m)
    distinct = {pts for _, pts in found}
    bad_inj = sum(1 for _, pts in found if not C.is_valid(rects, pts))
    bad_narrow = sum(1 for _, pts in found
                     if verify_narrow.collision(narrow, verify_narrow.mask(pts, m)) is not None)
    status = ('capped' if len(found) >= a.cap else
              'unresolved: time cap' if time.time() > deadline else 'complete')
    out = {'grid': {'rows': H, 'cols': m}, 'target_size': m + 6,
           'method': 'depth-first search over column letters under the equality structure, '
                     'every blackout rechecked by definition', 'cap': a.cap,
           'coordinates': 'one-based (column, row), (1,1) top-left', 'status': status,
           'found': len(found), 'distinct': len(distinct),
           'per_two_row_side': {','.join(str(r + 1) for r in k): v for k, v in per.items()},
           'failing_injectivity': bad_inj, 'failing_verify_narrow': bad_narrow,
           'search_seconds': round(search_seconds, 2), 'wall_seconds': round(time.time() - t0, 2),
           'first_models': [C.one_based(pts) for _, pts in found[:20]]}
    if len(found) <= 500:
        out['models'] = [{'points': C.one_based(pts)} for _, pts in found]
    tag = a.tag or f'w{m}_cap{a.cap}'
    with open(os.path.join(DATA, f'verify21_enum_{tag}.json'), 'w') as f:
        json.dump(out, f, indent=1)
    print({k: v for k, v in out.items() if k not in ('first_models', 'models')})


if __name__ == '__main__':
    main()
