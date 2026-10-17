"""Independent exact count of the maximum blackouts of the h x m grid attaining the row bound
m + floor(h^2/4), for h = 4 and h = 5, under the equality structure of the row bound: every
column is black in one row except floor(h^2/4) columns black in two rows, whose row pairs are
the edges of a balanced complete bipartite graph on the rows, each edge in exactly one column.

Method: a column-by-column transfer count. The alphabet is the singleton rows plus the edges of
the fixed row partition. A tilted rectangle on h rows occupies at most W+1 consecutive columns,
W computed from the right-angle-triple enumerator (every tilted rectangle of a wide grid is a
translate of one of the templates, which is checked). The state after a column consists of
  - the letters of the last W columns,
  - the presentations (visible corner sets of size one or two, positions relative to the
    current column) of the tilted rectangles completed so far whose points all lie in the last
    W columns, so that a tilted rectangle completed later could still present the same set,
  - the set of edges already used and whether a fully hidden rectangle has occurred.
When a column is added, every template whose rightmost column is the new one is examined:
a hidden rectangle is allowed once; a presentation of three or more corners is unique; a
presentation V of one or two corners is rejected when an axis rectangle also presents V (under
the equality structure, derived in the comments of axis_rival below) or when another tilted
rectangle presents V (stored, or completing in the same column). Axis rectangles never present
alike under the equality structure (an axis rectangle is never hidden, and two axis rectangles
with the same visible set of one or two corners would need one edge in two columns or a
triangle in the bipartite graph), so only tilted rectangles need to be examined.

The per-column analysis depends only on the letters of the last W+1 columns, so it is cached
on that key. The counts of all (used edges, hidden flag) combinations belonging to one
(window, presentations) key are kept in one integer, 64 bits per combination, so that using an
edge or recording a hidden rectangle is a mask and a shift of that integer.

Options restrict the singleton rows or fix the columns of the doubles. Counts are reported per
row partition; rows and columns in the output are one-based, the code is zero-based inside.

Usage: python verify21_count_check.py HEIGHT WIDTH [WIDTH ...] [--singleton-rows 1,5]
       [--double-columns 1,5,9,13,17,21] [--minutes 20] [--tag NAME]
"""
import argparse
import json
import os
import sys
import time
from collections import defaultdict
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import verify21_common_check as C  # noqa: E402

DATA = os.path.join(HERE, '..', 'data')
B = 64                       # bits per (used edges, hidden) slot


def templates(h):
    """Tilted rectangles on h rows, normalised to leftmost column 0: list of (span, corners)."""
    wide = 4 * h + 4
    shapes = set()
    for rect in C.rectangles(h, wide):
        if C.is_axis(rect):
            continue
        x0 = min(x for x, _ in rect)
        shapes.add(tuple(sorted((x - x0, y) for x, y in rect)))
    W = max(max(dx for dx, _ in s) for s in shapes)
    for m in (wide + 3, 2 * wide):       # completeness at two further widths
        tilted = {r for r in C.rectangles(h, m) if not C.is_axis(r)}
        translates = {frozenset((dx + t, y) for dx, y in s)
                      for s in shapes for t in range(m - max(dx for dx, _ in s))}
        assert tilted == translates, (h, m)
    return W, sorted((max(dx for dx, _ in s), s) for s in shapes)


def axis_rival(V, blackset, edges, h):
    """Does an axis rectangle present exactly V (|V| in {1, 2}) in the final blackout?
    blackset holds the black points of the examined span (V's columns lie inside it).
      V = {(x,r),(x,s)}: the rival has columns x and z, z the column carrying edge {r,s}; it
          exists iff {r,s} is an edge (the edge column is not x, where r and s are visible).
      V = {(x,r),(z,r)}, x != z: rival rows {r,s} with (x,s) and (z,s) black for some s.
      V = {(x,r),(z,s)}, x != z, r != s: rival rows {r,s}, columns x, z, with (x,s), (z,r) black.
      V = {(x,r)}: rival columns x, z with (x,s) black and z carrying edge {r,s}; it exists iff
          some row s black in column x has {r,s} an edge.
    Every column of the final blackout is black in one or two rows, so a column carries the
    edge {r,s} iff it is black in both r and s, and then no other column is."""
    pts = sorted(V)
    if len(pts) == 1:
        (x, r), = pts
        return any((x, s) in blackset and frozenset((r, s)) in edges for s in range(h) if s != r)
    (x, r), (z, s) = pts
    if x == z:
        return frozenset((r, s)) in edges
    if r == s:
        return any((x, t) in blackset and (z, t) in blackset for t in range(h) if t != r)
    return (x, s) in blackset and (z, r) in blackset


def count(h, m, two_rows, singleton_rows, double_columns, W, temps, deadline):
    other = [r for r in range(h) if r not in two_rows]
    edge_list = [frozenset((a, b)) for a in two_rows for b in other]
    edges = set(edge_list)
    n_e = len(edge_list)
    full = (1 << n_e) - 1
    # letters: 0..h-1 singleton rows, h.. edges
    rows_of = [frozenset((r,)) for r in range(h)] + edge_list
    singles = list(singleton_rows)
    edge_letters = list(range(h, h + n_e))
    n_slots = (1 << n_e) * 2
    slot = (1 << B) - 1
    mask_h0 = sum(slot << (B * s) for s in range(0, n_slots, 2))
    mask_all = (1 << (B * n_slots)) - 1
    mask_not_e = [sum(slot << (B * s) for s in range(n_slots) if not ((s >> 1) >> i) & 1)
                  for i in range(n_e)]
    # a presentation is an integer: bit (dx + W) * h + y for the point (dx, y), dx in [-W, 0]
    low = (1 << h) - 1

    def bit(dx, y):
        return 1 << ((dx + W) * h + y)

    cache = {}

    def analyse(window, letter):
        """window: letters of columns col-W..col-1 (-1 before the grid), letter: column col.
        None if rejected, else (hidden_count, presentations) with presentations the tuple of
        visible sets of size 1 or 2, as integers."""
        key = (window, letter)
        if key in cache:
            return cache[key]
        cols = window + (letter,)              # index i -> column col - W + i
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
            if axis_rival(vis, blackset, edges, h) or vis in pres:
                ok = False
                break
            pres.append(vis)
        result = None
        if ok and hidden <= 1:
            result = (hidden, tuple(sum(bit(x - W, y) for x, y in v) for v in pres))
        cache[key] = result
        return result

    match_cache = {}

    def matchable(window, v):
        """Can a tilted rectangle completing in a later column present exactly v? window holds
        the letters of the last W columns (dx = -(W-1)..0); the rectangle's corners in those
        columns other than v's points must be black, its later corners are free."""
        key = (window, v)
        if key in match_cache:
            return match_cache[key]
        pts = {(i // h - W, i % h) for i in range(v.bit_length()) if v >> i & 1}
        black = {(i - (W - 1), y) for i, L in enumerate(window) if L >= 0 for y in rows_of[L]}
        found = False
        for span, corners in temps:
            for left in range(-(W - 1), 1):
                if left + span < 1:
                    continue
                placed = {(left + dx, y) for dx, y in corners}
                if not pts <= placed:
                    continue
                if all(p in black for p in placed - pts if p[0] <= 0):
                    found = True
                    break
            if found:
                break
        match_cache[key] = found
        return found

    states = {((-1,) * W, ()): 1}     # slot (used=0, hidden=0)
    max_keys = 0
    for col in range(m):
        if time.time() > deadline:
            return None, max_keys
        new = defaultdict(int)
        if double_columns is None:
            letters = singles + edge_letters
        elif col in double_columns:
            letters = edge_letters
        else:
            letters = singles
        for (window, pending), packed in states.items():
            shifted = [v >> h for v in pending]
            for letter in letters:
                res = analyse(window, letter)
                if res is None:
                    continue
                dh, pres = res
                if any(v in shifted for v in pres):
                    continue
                nwindow = window[1:] + (letter,)
                npending = tuple(sorted(v for v in shifted + list(pres)
                                        if not v & low and matchable(nwindow, v)))
                value = packed
                if letter >= h:
                    i = letter - h
                    value = (value & mask_not_e[i]) << (B * 2 * (1 << i))
                if dh:
                    value = (value & mask_h0) << B
                value &= mask_all
                if value:
                    new[(nwindow, npending)] += value
        states = new
        max_keys = max(max_keys, len(states))
    total = 0
    for packed in states.values():
        total += (packed >> (B * full * 2)) & slot
        total += (packed >> (B * (full * 2 + 1))) & slot
    return total, max_keys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('height', type=int)
    ap.add_argument('widths', type=int, nargs='+')
    ap.add_argument('--singleton-rows', default=None)
    ap.add_argument('--double-columns', default=None)
    ap.add_argument('--minutes', type=float, default=20.0)
    ap.add_argument('--tag', default=None)
    a = ap.parse_args()
    h = a.height
    srows = list(range(h)) if a.singleton_rows is None else \
        [int(t) - 1 for t in a.singleton_rows.split(',')]
    dcols = None if a.double_columns is None else \
        {int(t) - 1 for t in a.double_columns.split(',')}
    W, temps = templates(h)
    tag = a.tag or (f'h{h}_w' + '_'.join(map(str, a.widths)) +
                    ('' if a.singleton_rows is None else '_srows' + a.singleton_rows.replace(',', '')) +
                    ('' if a.double_columns is None else '_dcols'))
    out = {'method': 'transfer count over column letters with pending presentations '
                     '(verify21_count_check.py docstring)',
           'hypothesis': 'equality structure of the row bound', 'height': h,
           'tilted_span_W': W, 'tilted_templates': len(temps),
           'python_version': sys.version.split()[0],
           'coordinates': 'one-based rows and columns', 'results': []}
    deadline = time.time() + 60 * a.minutes
    for m in a.widths:
        t0 = time.time()
        per = []
        total = 0
        status = 'complete'
        for two in combinations(range(h), h // 2):
            if h % 2 == 0 and 0 not in two:
                continue              # unordered partition: take the side containing row 1
            t1 = time.time()
            n, mk = count(h, m, two, srows, dcols, W, temps, deadline)
            if n is None:
                status = 'unresolved: time cap'
                break
            per.append({'two_rows': [r + 1 for r in two], 'count': n, 'max_keys': mk,
                        'seconds': round(time.time() - t1, 2)})
            total += n
        rec = {'width': m, 'target_size': m + (h * h) // 4,
               'singleton_rows_allowed': [r + 1 for r in srows],
               'double_columns': None if dcols is None else sorted(c + 1 for c in dcols),
               'per_partition': per, 'count': total if status == 'complete' else None,
               'status': status, 'seconds': round(time.time() - t0, 2)}
        out['results'].append(rec)
        print(m, rec['count'], status, rec['seconds'], [p['count'] for p in per], flush=True)
        with open(os.path.join(DATA, f'verify21_count_{tag}.json'), 'w') as f:
            json.dump(out, f, indent=1)
        if status != 'complete':
            break


if __name__ == '__main__':
    main()
