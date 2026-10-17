"""Definitional count of the maximum blackouts of small h x m grids, assuming nothing about
their structure: a depth-first search over the columns, each column taking any subset of the
rows, pruned by three necessary conditions and finished by the full test.

Pruning: (1) two columns never share two black rows and three columns never share rows pairwise
in three distinct pairs (the axis-rectangle condition, PROBLEM.md: no 4- or 6-cycle in the
row-column incidence graph; checked here against the full test on every blackout of small
grids); (2) rectangles lying entirely in the processed columns have their final visible corner
sets, which must be distinct and at most one of them empty; (3) the remaining columns cannot
bring the total to the target, counting that distinct columns use disjoint row pairs. Every surviving set is tested with the injectivity of the
visible-corner map over all rectangles (right-angle-triple enumerator) and with
verify_narrow.collision. Output counts per grid, and the optima themselves (one-based) when
there are at most 500 of them.

Usage: python verify21_brute_check.py HEIGHT WIDTH [WIDTH ...] [--minutes 20]
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
import verify_narrow  # noqa: E402

DATA = os.path.join(HERE, '..', 'data')


def no_short_cycles(colsets):
    pairs = {}
    for i, a in enumerate(colsets):
        for j in range(i):
            common = a & colsets[j]
            if len(common) >= 2:
                return False
            if common:
                pairs[i, j] = next(iter(common))
    for (i, j), r in pairs.items():
        for (k, l), s in pairs.items():
            if r == s or (k, l) <= (i, j):
                continue
            # two of the three columns i,j,k,l coincide and a third pair closes a 6-cycle
            share = {i, j} & {k, l}
            if len(share) != 1:
                continue
            a = ({i, j} - share).pop()
            b = ({k, l} - share).pop()
            key = (max(a, b), min(a, b))
            if key in pairs and pairs[key] not in (r, s):
                return False
    return True


def count_grid(h, m, deadline):
    target = m + (h * h) // 4
    rects = C.rectangles(h, m)
    by_right = [[] for _ in range(m)]
    for r in rects:
        by_right[max(x for x, _ in r)].append(r)
    subsets = [frozenset(s) for k in range(h + 1) for s in combinations(range(h), k)]
    found = []
    nodes = 0

    def dfs(col, colsets, black, seen, hidden):
        nonlocal nodes
        nodes += 1
        if nodes % 20000 == 0 and time.time() > deadline:
            raise TimeoutError
        if col == m:
            if len(black) == target:
                found.append(frozenset(black))
            return
        remaining = m - col
        pairs_used = sum(len(c) * (len(c) - 1) // 2 for c in colsets)
        for s in subsets:
            # columns use disjoint row pairs (no 4-cycle), at most h(h-1)/2 in all; a column
            # with k black points adds k - 1 beyond one per column at the cost of k(k-1)/2 pairs
            budget = h * (h - 1) // 2 - pairs_used - len(s) * (len(s) - 1) // 2
            if budget < 0:
                continue
            if len(black) + len(s) + (remaining - 1) + min(budget, remaining - 1) < target:
                continue
            if len(black) + len(s) > target:
                continue
            nsets = colsets + [s]
            if not no_short_cycles(nsets):
                continue
            nblack = black | {(col, y) for y in s}
            nseen = dict(seen)
            nhidden = hidden
            ok = True
            for r in by_right[col]:
                vis = frozenset(p for p in r if p not in nblack)
                if not vis:
                    nhidden += 1
                    if nhidden > 1:
                        ok = False
                        break
                    continue
                if vis in nseen:
                    ok = False
                    break
                nseen[vis] = r
            if ok:
                dfs(col + 1, nsets, nblack, nseen, nhidden)

    dfs(0, [], set(), {}, 0)
    optima = [b for b in found if C.is_valid(rects, b)]
    narrow = [b for b in found if verify_narrow.collision(
        verify_narrow.rectangles(h, m), verify_narrow.mask(b, m)) is None]
    assert set(optima) == set(narrow)
    return len(found), optima, nodes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('height', type=int)
    ap.add_argument('widths', type=int, nargs='+')
    ap.add_argument('--minutes', type=float, default=20.0)
    a = ap.parse_args()
    deadline = time.time() + 60 * a.minutes
    out = {'method': 'definitional depth-first search over columns, no structural hypothesis',
           'coordinates': 'one-based (column, row)', 'results': []}
    tag = f'h{a.height}_w' + '_'.join(map(str, a.widths))
    for m in a.widths:
        t0 = time.time()
        try:
            survivors, optima, nodes = count_grid(a.height, m, deadline)
            shapes = [C.equality_shape(b, a.height, m) for b in optima]
            rec = {'height': a.height, 'width': m, 'target_size': m + (a.height ** 2) // 4,
                   'dfs_survivors': survivors, 'optima': len(optima), 'nodes': nodes,
                   'all_have_equality_structure': all(s is not None for s in shapes),
                   'per_two_row_side': {}, 'status': 'complete',
                   'seconds': round(time.time() - t0, 2)}
            for s in shapes:
                if s is not None:
                    key = ','.join(str(r + 1) for r in s[0])
                    rec['per_two_row_side'][key] = rec['per_two_row_side'].get(key, 0) + 1
            if len(optima) <= 500:
                rec['optima_points'] = [C.one_based(b) for b in optima]
        except TimeoutError:
            rec = {'height': a.height, 'width': m, 'status': 'unresolved: time cap',
                   'seconds': round(time.time() - t0, 2)}
        out['results'].append(rec)
        print({k: v for k, v in rec.items() if k != 'optima_points'}, flush=True)
        with open(os.path.join(DATA, f'verify21_brute_{tag}.json'), 'w') as f:
            json.dump(out, f, indent=1)
        if rec['status'] != 'complete':
            break


if __name__ == '__main__':
    main()
