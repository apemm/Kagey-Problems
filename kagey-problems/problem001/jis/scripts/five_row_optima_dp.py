"""Exact count of the maximum blackouts of an h x m grid that attain the row bound
m + floor(h^2/4), by a transfer count over column letters (h = 4 or 5).

Hypothesis (the equality theorem of the row bound, proved in the research notes): a blackout
of m + floor(h^2/4) points has every column black in exactly one row, except floor(h^2/4)
columns black in exactly two rows whose row pairs are the edges of a balanced complete
bipartite graph on the rows, each edge used in exactly one column. Axis-aligned rectangles are
then automatically identifiable, so only pairs involving a tilted rectangle can present alike,
and two rectangles present alike only if the common presentation has at most two points.

A column is a letter: a singleton row or an edge. A tilted rectangle on h rows spans at most
W = 1 + floor((h-1)^2/4) columns beyond its leftmost one (checked against verify_narrow's
enumerator at start-up). Columns are read left to right; the state after column c is
  (the letters of columns c-W+1..c,
   the presentations of size one or two of the tilted rectangles already completed that a
   tilted rectangle completing later could still present,
   the set of edges used so far, and whether a fully hidden rectangle has occurred).
The last two components are packed into one integer per (window, presentations) key, one
slot per (edge subset, hidden flag), so a column transition is a mask and a shift.

Adding column c completes every tilted rectangle whose rightmost column is c. For each with
visible corner set V:
  |V| >= 3: nothing (three corners determine a rectangle);
  |V| = 0: a hidden rectangle; two of them reject (an axis rectangle is never hidden, since
           the two columns would carry the same row pair);
  |V| in {1,2}: reject if an axis rectangle presents V, which happens exactly when
      V = {(x,r),(x,s)}: {r,s} is an edge (every edge occurs in some other column);
      V = {(x,r),(z,r)}: some row s != r is black in both columns x and z;
      V = {(x,r),(z,s)}: row s is black in column x and row r in column z;
      V = {(x,r)}: some row s black in column x has {r,s} an edge;
    and reject if another tilted rectangle presents V (one completed earlier and still
    stored, or one completing in the same column).
A stored presentation is dropped once no tilted rectangle completing later can present it
(its columns would have to be among the last W-1, and its black corners inside the window
must already be black). The count is the sum over final states that used every edge.

Options restrict the singleton rows or fix the columns of the doubles, which are the
sub-families compared with the SAT enumerations. Rows and columns in the output are
one-based; the code is zero-based inside.

Usage: python five_row_optima_dp.py HEIGHT WIDTH [WIDTH ...] [--singleton-rows 1] [--double-columns 1,5,9,13,17,21]
       [--minutes 30] [--out FILE] [--tag NAME]
"""
import argparse
import json
import os
import sys
import time
from collections import defaultdict
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, ROOT)
import verify_narrow  # noqa: E402

DATA_DIR = os.path.join(HERE, '..', 'data')


def tilted_templates(h):
    """Tilted rectangles on h rows, normalised to leftmost column 0, as (span, corners)."""
    cols = 2 * h + 2
    axis = set(verify_narrow.axis_rectangles(h, cols))
    out = set()
    for r in verify_narrow.rectangles(h, cols):
        if r in axis:
            continue
        pts = [(x, y) for y in range(h) for x in range(cols) if r >> (y * cols + x) & 1]
        x0 = min(x for x, _ in pts)
        if max(x for x, _ in pts) - x0 > h:
            continue      # cannot happen for h <= 6; spans are checked below anyway
        out.add(tuple(sorted((x - x0, y) for x, y in pts)))
    templates = sorted((max(dx for dx, _ in t), t) for t in out)
    # completeness: every tilted rectangle of a wide grid is a translate of a template
    wide = 3 * h + 4
    axis_w = set(verify_narrow.axis_rectangles(h, wide))
    seen = set()
    for r in verify_narrow.rectangles(h, wide):
        if r in axis_w:
            continue
        pts = [(x, y) for y in range(h) for x in range(wide) if r >> (y * wide + x) & 1]
        x0 = min(x for x, _ in pts)
        seen.add(tuple(sorted((x - x0, y) for x, y in pts)))
    assert seen == out, 'template list incomplete'
    return templates


class Transfer:
    def __init__(self, h, W, templates, edges, singleton_rows):
        self.h, self.W = h, W
        self.edges = list(edges)                       # (a, b) zero-based, a < b
        self.edge_set = set(self.edges)
        self.k = len(self.edges)
        self.letters = [(1 << r, 0) for r in singleton_rows] + \
                       [((1 << a) | (1 << b), 1 << i) for i, (a, b) in enumerate(self.edges)]
        self.completing = [(W - span, t) for span, t in templates]     # leftmost index in win
        self.future = []                                               # for matchable()
        for span, t in templates:
            for lo in range(-(W - 1), 1):
                if lo + span >= 1:
                    self.future.append(tuple((lo + dx, y) for dx, y in t))
        self.trans_memo = {}
        self.match_memo = {}

    def matchable(self, window, pres):
        """Could a tilted rectangle with rightmost column > c present exactly pres?
        window: W masks for columns c-W+1..c; pres: frozenset of (offset <= 0, row)."""
        key = (window, pres)
        r = self.match_memo.get(key)
        if r is not None:
            return r
        W = self.W
        ok = False
        for corners in self.future:
            if not all(p in corners for p in pres):
                continue
            good = True
            for o, y in corners:
                if o > 0:
                    continue
                col = window[W - 1 + o]
                if col is None:
                    good = False
                    break
                black = col >> y & 1
                if black == ((o, y) in pres):
                    good = False
                    break
            if good:
                ok = True
                break
        self.match_memo[key] = ok
        return ok

    def step(self, window, pres, mask):
        """One column added. Returns None (rejected for every edge subset) or
        (new_window, new_pres, hidden_now)."""
        W, E = self.W, self.edge_set
        win = window + (mask,)
        hidden = 0
        new = []
        for k0, t in self.completing:
            vis = []
            dead = False
            for dx, y in t:
                col = win[k0 + dx]
                if col is None:
                    dead = True
                    break
                if not col >> y & 1:
                    vis.append((k0 + dx - W, y))
            if dead or len(vis) >= 3:
                continue
            if not vis:
                hidden += 1
                continue
            if len(vis) == 2:
                (o1, r1), (o2, r2) = vis
                if o1 == o2:
                    if (min(r1, r2), max(r1, r2)) in E:
                        return None
                elif r1 == r2:
                    if win[W + o1] & win[W + o2] & ~(1 << r1):
                        return None
                else:
                    if win[W + o1] >> r2 & 1 and win[W + o2] >> r1 & 1:
                        return None
            else:
                (o1, r1), = vis
                col = win[W + o1]
                for s in range(self.h):
                    if s != r1 and col >> s & 1 and (min(r1, s), max(r1, s)) in E:
                        return None
            new.append(frozenset(vis))
        if hidden >= 2:
            return None
        if len(set(new)) < len(new):
            return None
        shifted = [frozenset((o - 1, y) for o, y in p) for p in pres]
        newset = set(new)
        for p in shifted:
            if p in newset:
                return None
        window2 = win[1:]
        kept = []
        for p in shifted + new:
            if min(o for o, _ in p) < -(W - 1):
                continue
            if self.matchable(window2, p):
                kept.append(p)
        return window2, frozenset(kept), hidden

    def transitions(self, window, pres):
        key = (window, pres)
        r = self.trans_memo.get(key)
        if r is None:
            r = []
            for li, (mask, bit) in enumerate(self.letters):
                res = self.step(window, pres, mask)
                if res is not None:
                    r.append((li, bit, res[0], res[1], res[2]))
            self.trans_memo[key] = r
        return r

    def count(self, m, deadline, double_columns=None):
        """Number of valid words of length m using every edge once; None if the deadline
        passes. double_columns: set of zero-based columns that must carry the doubles."""
        k, W = self.k, self.W
        SW = 80
        nslots = 2 << k
        slot = (1 << SW) - 1

        def where(pred):
            v = 0
            for i in range(nslots):
                if pred(i >> 1, i & 1):
                    v |= slot << (i * SW)
            return v
        without = {bit: where(lambda u, hd, b=bit: not u & b) for _, bit in self.letters if bit}
        hidden0 = where(lambda u, hd: hd == 0)
        need = [where(lambda u, hd, j=j: bin(u).count('1') >= j) for j in range(k + 1)]
        allused = (1 << k) - 1
        final = where(lambda u, hd: u == allused)

        dp = {((None,) * W, frozenset()): 1}
        max_states = 1
        for c in range(m):
            if time.time() > deadline:
                return None, max_states
            nxt = defaultdict(int)
            remaining = m - c - 1
            needmask = need[max(0, k - remaining)]
            if double_columns is not None:
                want_double = c in double_columns
            for (window, pres), vec in dp.items():
                for li, bit, window2, pres2, hidden in self.transitions(window, pres):
                    if double_columns is not None and bool(bit) != want_double:
                        continue
                    v = vec
                    if bit:
                        v = (v & without[bit]) << (2 * bit * SW)
                    if hidden:
                        v = (v & hidden0) << SW
                    v &= needmask
                    if v:
                        nxt[(window2, pres2)] += v
            dp = nxt
            max_states = max(max_states, len(dp))
        total = 0
        for vec in dp.values():
            v = vec & final
            while v:
                total += v & slot
                v >>= SW
        return total, max_states


def balanced_partitions(h):
    a = h // 2
    out = []
    for A in combinations(range(h), a):
        B = tuple(r for r in range(h) if r not in A)
        if 2 * a == h and A > B:
            continue
        out.append((A, B))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('height', type=int)
    ap.add_argument('widths', type=int, nargs='+')
    ap.add_argument('--singleton-rows', default=None, help='one-based rows allowed for singletons')
    ap.add_argument('--double-columns', default=None, help='one-based columns that carry the doubles')
    ap.add_argument('--minutes', type=float, default=30.0, help='wall-clock cap per width')
    ap.add_argument('--out', default=None)
    ap.add_argument('--tag', default='')
    args = ap.parse_args()
    h = args.height
    assert h in (4, 5)
    W = 1 + ((h - 1) ** 2) // 4
    templates = tilted_templates(h)
    assert max(span for span, _ in templates) <= W, 'tilted span bound violated'
    srows = list(range(h)) if not args.singleton_rows else \
        [int(r) - 1 for r in args.singleton_rows.split(',')]
    dcols = None if not args.double_columns else \
        {int(c) - 1 for c in args.double_columns.split(',')}
    results = []
    for m in args.widths:
        t0 = time.time()
        deadline = t0 + 60 * args.minutes
        entry = {'height': h, 'width': m, 'target_size': m + (h * h) // 4,
                 'singleton_rows_allowed': [r + 1 for r in srows],
                 'double_columns': None if dcols is None else sorted(c + 1 for c in dcols),
                 'per_partition': [], 'count': 0, 'status': 'complete'}
        for A, B in balanced_partitions(h):
            edges = sorted(tuple(sorted((a, b))) for a in A for b in B)
            if dcols is not None and len(dcols) != len(edges):
                raise SystemExit('wrong number of double columns')
            tr = Transfer(h, W, templates, edges, srows)
            t1 = time.time()
            n, states = tr.count(m, deadline, dcols)
            rec = {'rows_a': [r + 1 for r in A], 'rows_b': [r + 1 for r in B],
                   'count': n, 'max_states': states,
                   'transition_keys': len(tr.trans_memo), 'seconds': round(time.time() - t1, 2)}
            entry['per_partition'].append(rec)
            if n is None:
                entry['status'] = 'unresolved: wall-clock cap reached'
                entry['count'] = None
                break
            entry['count'] += n
        entry['seconds'] = round(time.time() - t0, 2)
        results.append(entry)
        print(f'h={h} m={m}: {entry["count"]} ({entry["status"]}, {entry["seconds"]} s) '
              + ', '.join(str(p['count']) for p in entry['per_partition']), flush=True)
    tag = args.tag
    if not tag:
        tag = f'h{h}_w' + '_'.join(str(m) for m in args.widths)
        if args.singleton_rows:
            tag += '_srows' + args.singleton_rows.replace(',', '')
        if args.double_columns:
            tag += '_dcols' + args.double_columns.replace(',', '-')
    out = args.out or os.path.join(DATA_DIR, f'five_row_optima_dp_{tag}.json')
    payload = {'method': 'transfer count over column letters with stored presentations '
                         '(see the script docstring)',
               'hypothesis': 'equality structure of the row bound (balanced complete bipartite '
                             'row pairs, each edge once, singletons elsewhere)',
               'height': h, 'tilted_span_bound_W': W, 'tilted_templates': len(templates),
               'python_version': sys.version.split()[0],
               'coordinates': 'one-based rows and columns where named',
               'wall_cap_minutes_per_width': args.minutes,
               'results': results}
    with open(out, 'w') as f:
        json.dump(payload, f, indent=1)
    print('->', out)


if __name__ == '__main__':
    main()
