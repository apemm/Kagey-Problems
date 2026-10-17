"""Exact count of the blackouts attaining the row bound m + floor(h^2/4) on an h x m grid, by a
window dynamic programme over column states.

Equality structure (from the row-bound proof: the row-column incidence graph has no 4- or
6-cycle, replacing each column by a tree on its black rows gives a simple triangle-free graph
on the rows, and Mantel's theorem applies). For h >= 4 every column is black in exactly one
row except floor(h^2/4) columns black in exactly two rows, and those row pairs are the edges of
the balanced complete bipartite graph on a partition of the rows, each edge in exactly one
column (a column with three black rows would force a 6-cycle). For h = 3 there is a second
class: one column black in all three rows and singletons elsewhere. The axis-aligned
rectangles are then automatically identifiable (no 4- or 6-cycle), so only pairs involving a
tilted rectangle remain. A tilted rectangle spans at most W_h = 1 + floor((h-1)^2/4) columns
beyond its leftmost one (2, 3, 5 for h = 3, 4, 5), and two rectangles present alike only if
the presentation has at most two points (three visible corners determine a rectangle).

Scan columns left to right. The state after column c is (states of columns c-W+1..c, the set
of non-singleton states used so far, whether a fully hidden rectangle has been completed, and
the presentations of size one or two of tilted rectangles completed so far whose leftmost
column is c-W or earlier and whose visible corners all lie in columns >= c-W+1; the
presentations of tilted rectangles inside the stored window are recomputed from it). Adding
column c completes every tilted rectangle whose rightmost column is c. For each one with
visible set V:
  |V| >= 3: nothing to check;
  |V| = 0: reject if a hidden rectangle was already completed (two empty presentations);
  |V| in {1, 2}: reject if an axis rectangle presents the same V, by the exact tests
      {(x,r),(x,s)}: {r,s} is a black row pair of some column;
      {(x,r),(z,r)}, x != z: some row s != r is black in both columns x and z;
      {(x,r),(z,s)}, x != z, r != s: s is black in column x and r in column z;
      {(x,r)}: some row s black in column x has {r,s} a black row pair of some column;
    (every black row pair is an edge of the fixed bipartite graph, used exactly once, so these
    tests are decided locally), and reject if another tilted rectangle presents the same V.
The count sums the final states that used every edge. Coordinates inside are zero-based; the
output names rows one-based.

Validation targets (ledger): h = 3: 53, 224, 892, 3420, 12704, 45864, 161992 for m = 3..9;
h = 4: 26, 292 for m = 6, 7; h = 5: 4, 44, 350 for m = 8, 9, 10 (SAT enumeration, jis/data).

Usage: python row_bound_count_dp.py HEIGHT WIDTH [WIDTH ...] [--singleton-rows 1,5] [--out FILE]
"""
import argparse
import json
import os
import sys
import time
from collections import defaultdict
from functools import lru_cache
from itertools import combinations

from five_row_common import DATA_DIR, verify_narrow


def tilted_templates(h, W):
    """Tilted rectangles on h rows with leftmost column 0, as (span, corners) with corners a
    tuple of (dx, y); from verify_narrow.rectangles on an h x (W+1) grid minus the axis ones."""
    cols = W + 1
    axis = set(verify_narrow.axis_rectangles(h, cols))
    out = set()
    for r in verify_narrow.rectangles(h, cols):
        if r in axis:
            continue
        pts = [(x, y) for y in range(h) for x in range(cols) if r >> (y * cols + x) & 1]
        x0 = min(x for x, _ in pts)
        out.add(tuple(sorted((x - x0, y) for x, y in pts)))
    return [(max(dx for dx, _ in t), t) for t in sorted(out)]


class Counter:
    def __init__(self, h, W, templates, F, singleton_rows):
        self.h, self.W, self.templates = h, W, templates
        self.F = F                                   # set of (r, s) sorted pairs
        self.singleton_rows = singleton_rows
        # placements inside a (W+1)-column window: (leftmost index k0, span, corners)
        self.placements = [(k0, span, t) for span, t in templates for k0 in range(W + 1 - span)]
        self.analyse = lru_cache(maxsize=None)(self._analyse)
        self.matchable = lru_cache(maxsize=None)(self._matchable)

    def _matchable(self, window, pres):
        """window: W row bitmasks for columns c-W+1..c; pres: presentation with offsets
        relative to c. True if some tilted rectangle with rightmost column > c and leftmost
        column >= c-W+1 could present exactly pres: its corners in the window are black except
        those of pres, which are white. Presentations failing this can never collide again."""
        W = self.W
        for span, t in self.templates:
            for lo in range(-(W - 1), 1):
                if lo + span <= 0:
                    continue
                corners = {(lo + dx, y) for dx, y in t}
                if not pres <= corners:
                    continue
                good = True
                for o, y in corners:
                    if o > 0:
                        continue
                    col = window[W - 1 + o]
                    if col is None or (col >> y & 1) == ((o, y) in pres):
                        good = False
                        break
                if good:
                    return True
        return False

    def _analyse(self, win6):
        """win6: tuple of W+1 row bitmasks (None outside the grid) for columns c-W..c.
        Returns None if a tilted rectangle completed at column c (index W) has an axis rival or
        presents like another tilted rectangle inside the window; otherwise
        (new_hidden, new_presentations, old_presentations, carried_presentations) where the
        presentations are frozensets of (offset relative to c, row) and 'carried' are those of
        rectangles with leftmost index 0 that fit in offsets >= -(W-1)."""
        W, F = self.W, self.F
        new_hidden = 0
        new, old, carried = [], [], []
        for k0, span, t in self.placements:
            if any(win6[k0 + dx] is None for dx, _ in t):
                continue
            vis = tuple((k0 + dx - W, y) for dx, y in t if not win6[k0 + dx] >> y & 1)
            completes_now = (k0 + span == W)
            if len(vis) >= 3:
                continue
            if not vis:
                if completes_now:
                    new_hidden += 1
                continue
            if completes_now:
                # axis rival tests
                if len(vis) == 2:
                    (o1, r1), (o2, r2) = vis
                    if o1 == o2:
                        if (min(r1, r2), max(r1, r2)) in F:
                            return None
                    elif r1 == r2:
                        common = win6[W + o1] & win6[W + o2] & ~(1 << r1)
                        if common:
                            return None
                    else:
                        if win6[W + o1] >> r2 & 1 and win6[W + o2] >> r1 & 1:
                            return None
                else:
                    (o1, r1), = vis
                    bx = win6[W + o1]
                    if any(bx >> s & 1 and (min(r1, s), max(r1, s)) in F
                           for s in range(self.h) if s != r1):
                        return None
            key = frozenset(vis)
            (new if completes_now else old).append(key)
            if k0 == 0 and min(o for o, _ in vis) >= -(W - 1):
                carried.append(key)
        if new_hidden >= 2:
            return None
        if len(set(new)) < len(new) or set(new) & set(old):
            return None
        return new_hidden, frozenset(new), frozenset(carried)

    def count_slow(self, m, specials):
        """Reference implementation: one dictionary entry per full state."""
        h, W = self.h, self.W
        alphabet = [(1 << r, 0) for r in self.singleton_rows]
        for i, s in enumerate(specials):
            alphabet.append((sum(1 << r for r in s), 1 << i))
        all_used = (1 << len(specials)) - 1
        dp = {((None,) * W, 0, False, frozenset()): 1}
        for c in range(m):
            nxt = defaultdict(int)
            remaining_after = m - c - 1
            for (window, used, hidden, extras), cnt in dp.items():
                shifted = None
                for mask, bit in alphabet:
                    if used & bit:
                        continue
                    nu = used | bit
                    if (all_used ^ nu).bit_count() > remaining_after:
                        continue
                    win6 = window + (mask,)
                    res = self.analyse(win6)
                    if res is None:
                        continue
                    new_hidden, new, carried = res
                    if new_hidden and hidden:
                        continue
                    if shifted is None:
                        shifted = frozenset(frozenset((o - 1, r) for o, r in p) for p in extras)
                    if new & shifted:
                        continue
                    window5 = win6[1:]
                    kept = frozenset(p for p in shifted | carried
                                     if min(o for o, _ in p) >= -(W - 1) and self.matchable(window5, p))
                    nxt[(win6[1:], nu, hidden or bool(new_hidden), kept)] += cnt
            dp = nxt
        total = sum(cnt for (window, used, hidden, extras), cnt in dp.items() if used == all_used)
        return total, len(dp)

    def count(self, m, specials):
        """Same dynamic programme keyed by (window, presentations) only; the counts for the
        2^k x 2 combinations of (used specials, hidden flag) are packed into one integer with
        SW-bit slots, slot index = 2*used + hidden, so a transition is a mask and a shift."""
        W = self.W
        k = len(specials)
        nslots = (1 << k) * 2
        SW = 128
        slot_mask = (1 << SW) - 1
        alphabet = [(1 << r, 0) for r in self.singleton_rows]
        for i, s in enumerate(specials):
            alphabet.append((sum(1 << r for r in s), 1 << i))
        all_used = (1 << k) - 1

        def slots_where(pred):
            v = 0
            for i in range(nslots):
                if pred(i >> 1, i & 1):
                    v |= slot_mask << (i * SW)
            return v
        without = {bit: slots_where(lambda u, hd: not u & bit) for _, bit in alphabet if bit}
        hidden0 = slots_where(lambda u, hd: hd == 0)
        min_pop = [slots_where(lambda u, hd, j=j: u.bit_count() >= j) for j in range(k + 1)]
        final = slots_where(lambda u, hd: u == all_used)

        dp = {((None,) * W, frozenset()): 1}       # slot 0: nothing used, not hidden
        for c in range(m):
            nxt = defaultdict(int)
            remaining_after = m - c - 1
            need = min_pop[max(0, k - remaining_after)]
            for (window, extras), vec in dp.items():
                shifted = frozenset(frozenset((o - 1, r) for o, r in p) for p in extras)
                for mask, bit in alphabet:
                    win6 = window + (mask,)
                    res = self.analyse(win6)
                    if res is None:
                        continue
                    new_hidden, new, carried = res
                    if new & shifted:
                        continue
                    v = vec
                    if bit:
                        v = (v & without[bit]) << (bit * 2 * SW)
                    if new_hidden:
                        v = (v & hidden0) << SW
                    v &= need
                    if not v:
                        continue
                    window5 = win6[1:]
                    kept = frozenset(p for p in shifted | carried
                                     if min(o for o, _ in p) >= -(W - 1) and self.matchable(window5, p))
                    nxt[(window5, kept)] += v
            dp = nxt
        total = 0
        for vec in dp.values():
            v = vec & final
            while v:
                total += v & slot_mask
                v >>= SW
        return total, len(dp)


def partitions_of(h):
    a = h // 2
    out = []
    for A in combinations(range(h), a):
        B = tuple(r for r in range(h) if r not in A)
        if a * 2 == h and A > B:
            continue
        out.append((A, B))
    return out


def count_row_bound_optima(h, m, templates=None, singleton_rows=None):
    W = 1 + ((h - 1) ** 2) // 4
    if templates is None:
        templates = tilted_templates(h, W)
    if singleton_rows is None:
        singleton_rows = list(range(h))
    detail = []
    total = 0
    for A, B in partitions_of(h):
        edges = tuple(sorted(tuple(sorted((a, b))) for a in A for b in B))
        n, states = Counter(h, W, templates, frozenset(edges), singleton_rows).count(m, edges)
        detail.append({'small_part_rows': [r + 1 for r in A], 'large_part_rows': [r + 1 for r in B],
                       'count': n, 'final_dp_states': states})
        total += n
    if h == 3:
        F = frozenset(((0, 1), (0, 2), (1, 2)))
        n, states = Counter(h, W, templates, F, singleton_rows).count(m, ((0, 1, 2),))
        detail.append({'class': 'one column black in all three rows', 'count': n,
                       'final_dp_states': states})
        total += n
    return total, detail


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('height', type=int)
    ap.add_argument('widths', type=int, nargs='+')
    ap.add_argument('--singleton-rows', default=None,
                    help='restrict singleton columns to these one-based rows, e.g. 1,5')
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    h = args.height
    W = 1 + ((h - 1) ** 2) // 4
    templates = tilted_templates(h, W)
    srows = None
    if args.singleton_rows:
        srows = [int(r) - 1 for r in args.singleton_rows.split(',')]
    results = []
    for m in args.widths:
        t0 = time.time()
        total, detail = count_row_bound_optima(h, m, templates, srows)
        dt = time.time() - t0
        results.append({'height': h, 'width': m, 'target_size': m + (h * h) // 4,
                        'singleton_rows_allowed': [r + 1 for r in (srows or range(h))],
                        'count': total, 'per_partition': detail, 'seconds': round(dt, 2)})
        print(f'h={h} m={m}: {total} row-bound optima ({dt:.1f} s); '
              + ', '.join(str(d['count']) for d in detail), flush=True)
    tag = f'_singletons{args.singleton_rows.replace(",", "")}' if args.singleton_rows else ''
    out = args.out or os.path.join(DATA_DIR, f'row_bound_counts_h{h}{tag}.json')
    payload = {'method': 'window dynamic programme over column states (see docstring)',
               'tilted_span_bound_W': W, 'tilted_templates': len(templates),
               'python_version': sys.version.split()[0],
               'coordinates': 'one-based rows where named', 'results': results}
    if os.path.exists(out):
        try:
            old = json.load(open(out))
            seen = {r['width'] for r in results}
            payload['results'] = [r for r in old.get('results', []) if r['width'] not in seen] + results
            payload['results'].sort(key=lambda r: r['width'])
        except Exception:
            pass
    with open(out, 'w') as f:
        json.dump(payload, f, indent=1)
    print('->', out)


if __name__ == '__main__':
    main()
