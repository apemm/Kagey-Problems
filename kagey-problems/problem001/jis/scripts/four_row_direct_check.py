"""Definitional recount of the four-row optimum numbers a_4(m).

A second, independently written enumeration of the maximum blackouts of the
4 x m grid (m + 4 black points), used to recheck the counts obtained from the
transfer machines and from the earlier candidate enumeration.

Rectangles are generated from right-angle triples: three grid points A, B, C
with (B - A) . (C - A) = 0 and B, C distinct from A and from each other give
the rectangle {A, B, C, B + C - A} when the fourth point lies in the grid.
The rectangle list is compared with verify_narrow.rectangles before use.

The search runs column by column and keeps the set of presentations (visible
corner sets) of every rectangle that lies inside the columns read so far.  A
prefix is abandoned as soon as two such rectangles share a presentation, since
the columns to the right cannot change the presentation of a rectangle that
does not meet them.  Two candidate spaces are available:

  full        every column carries any nonempty set of rows; a leaf is any
              blackout of exactly m + 4 points (prefixes with more than four
              excess points over the column count are cut, as are prefixes
              that can no longer reach four excess points);
  structured  four double columns carrying the four row pairs of a balanced
              2+2 row partition and one black point in every other column
              (the equality structure of the m + 4 bound).

Internally the grid is column major, bit 4*x + y for column x and row y, both
zero based.  All coordinates written out are one based (column, row) with
(1,1) the top left corner, as in verify_narrow.py.

Usage: python four_row_direct_check.py MODE WIDTH [WIDTH ...] [--cap SECONDS]
"""
import json
import os
import sys
import time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
PROBLEM = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, PROBLEM)
import verify_narrow  # noqa: E402

ROWS = 4
DATA = os.path.join(PROBLEM, 'jis', 'data')
PARTITIONS = {'{1,2}|{3,4}': ((0, 1), (2, 3)),
              '{1,3}|{2,4}': ((0, 2), (1, 3)),
              '{1,4}|{2,3}': ((0, 3), (1, 2))}


def rectangles_by_triples(rows, cols):
    """All non-degenerate rectangles with corners on the grid, as frozensets of (x, y)."""
    pts = [(x, y) for x in range(cols) for y in range(rows)]
    found = set()
    for a in pts:
        for b in pts:
            if b == a:
                continue
            for c in pts:
                if c == a or c == b:
                    continue
                if (b[0] - a[0]) * (c[0] - a[0]) + (b[1] - a[1]) * (c[1] - a[1]) != 0:
                    continue
                d = (b[0] + c[0] - a[0], b[1] + c[1] - a[1])
                if 0 <= d[0] < cols and 0 <= d[1] < rows:
                    found.add(frozenset((a, b, c, d)))
    return found


def bit(x, y):
    return 1 << (ROWS * x + y)


def to_narrow_mask(points, cols):
    return verify_narrow.mask(list(points), cols)


def rectangles_by_last_column(cols):
    """Rectangle bitmasks (column-major layout) grouped by their rightmost column."""
    rects = rectangles_by_triples(ROWS, cols)
    narrow = set(verify_narrow.rectangles(ROWS, cols))
    mine = {to_narrow_mask(r, cols) for r in rects}
    assert mine == narrow, 'rectangle lists differ from verify_narrow'
    by_col = [[] for _ in range(cols)]
    for r in rects:
        m = sum(bit(x, y) for x, y in r)
        by_col[max(x for x, _ in r)].append(m)
    return by_col, len(rects)


def points_of(column_masks):
    pts = []
    for x, m in enumerate(column_masks):
        for y in range(ROWS):
            if m >> y & 1:
                pts.append((x, y))
    return pts


def partition_of(column_masks):
    doubles = sorted(m for m in column_masks if bin(m).count('1') == 2)
    for name, (left, right) in PARTITIONS.items():
        edges = sorted((1 << a) | (1 << b) for a in left for b in right)
        if doubles == edges:
            return name
    return None


def one_based(points):
    return [[x + 1, y + 1] for x, y in sorted(points)]


class Search:
    def __init__(self, cols, mode, cap_seconds):
        self.cols = cols
        self.mode = mode
        self.by_col, self.n_rects = rectangles_by_last_column(cols)
        self.cap = cap_seconds
        self.start = time.time()
        self.nodes = 0
        self.leaves = 0
        self.timed_out = False
        self.seen = set()
        self.col_masks = [0] * cols
        self.counts = {}
        self.samples = {}
        self.odd_leaves = 0   # leaves whose column multiset is not the equality structure
        if mode == 'full':
            self.letters = list(range(1, 16))
        else:
            self.letters = [1, 2, 4, 8]

    def run(self, double_letters=None):
        self.double_letters = double_letters
        self._extend(0, 0, 0, 0)
        return not self.timed_out

    def _place(self, j, black):
        """Insert the presentations of rectangles ending at column j; undo and return False on a repeat."""
        added = []
        seen = self.seen
        for r in self.by_col[j]:
            vis = r & ~black
            if vis in seen:
                for v in added:
                    seen.discard(v)
                return False
            seen.add(vis)
            added.append(vis)
        self._added = added
        return True

    def _extend(self, j, black, excess, used):
        if self.timed_out:
            return
        self.nodes += 1
        if self.nodes % 100000 == 0 and time.time() - self.start > self.cap:
            self.timed_out = True
            return
        cols = self.cols
        if j == cols:
            if self.mode == 'full' and excess != 4:
                return
            self.leaves += 1
            cm = tuple(self.col_masks)
            name = partition_of(cm)
            if name is None or any(bin(m).count('1') > 2 for m in cm):
                self.odd_leaves += 1
                name = 'other'
            self.counts[name] = self.counts.get(name, 0) + 1
            if name not in self.samples:
                self.samples[name] = one_based(points_of(cm))
            return
        remaining = cols - j - 1
        if self.mode == 'full':
            for letter in self.letters:
                k = bin(letter).count('1')
                ex = excess + k - 1
                if ex > 4 or ex + 3 * remaining < 4:
                    continue
                nb = black | (letter << (ROWS * j))
                if self._place(j, nb):
                    added = self._added
                    self.col_masks[j] = letter
                    self._extend(j + 1, nb, ex, used)
                    for v in added:
                        self.seen.discard(v)
            return
        # structured: singles, and each double letter at most once, all four by the end
        unused = [i for i in range(4) if not used >> i & 1]
        if len(unused) > remaining + 1:
            return
        options = [(l, used) for l in self.letters] if len(unused) <= remaining else []
        for i in unused:
            options.append((self.double_letters[i], used | (1 << i)))
        for letter, nu in options:
            nb = black | (letter << (ROWS * j))
            if self._place(j, nb):
                added = self._added
                self.col_masks[j] = letter
                self._extend(j + 1, nb, excess, nu)
                for v in added:
                    self.seen.discard(v)


def recheck_sample(points_one_based, cols):
    pts = [(c - 1, r - 1) for c, r in points_one_based]
    black = verify_narrow.mask(pts, cols)
    assert black.bit_count() == cols + 4
    return verify_narrow.collision(verify_narrow.rectangles(ROWS, cols), black) is None


def main():
    cap = 1200.0
    args = []
    skip = False
    for a in sys.argv[1:]:
        if skip:
            cap = float(a)
            skip = False
        elif a == '--cap':
            skip = True
        else:
            args.append(a)
    mode = args[0]
    widths = [int(w) for w in args[1:]]
    out_path = os.path.join(DATA, f'four_row_direct_check_{mode}.json')
    results = {}
    if os.path.exists(out_path):
        results = json.load(open(out_path))
    for cols in widths:
        t0 = time.time()
        entry = {'width': cols, 'mode': mode, 'cap_seconds': cap}
        if mode == 'full':
            s = Search(cols, mode, cap)
            finished = s.run()
            entry.update(rectangles=s.n_rects, nodes=s.nodes, leaves=s.leaves,
                         counts=s.counts, non_equality_leaves=s.odd_leaves,
                         samples=s.samples, finished=finished)
            total = sum(s.counts.values()) if finished else None
        else:
            per = {}
            samples = {}
            nodes = 0
            finished = True
            for name, (left, right) in PARTITIONS.items():
                doubles = sorted((1 << a) | (1 << b) for a in left for b in right)
                s = Search(cols, mode, cap - (time.time() - t0))
                ok = s.run(doubles)
                nodes += s.nodes
                if not ok:
                    finished = False
                    per[name] = None
                    break
                assert s.odd_leaves == 0 and set(s.counts) <= {name}
                per[name] = s.counts.get(name, 0)
                if name in s.samples:
                    samples[name] = s.samples[name]
            entry.update(rectangles=s.n_rects, nodes=nodes, counts=per, samples=samples,
                         finished=finished)
            total = sum(per.values()) if finished else None
        entry['a4'] = total
        entry['seconds'] = round(time.time() - t0, 2)
        entry['status'] = 'resolved' if finished else 'unresolved (time cap)'
        for name, pts in entry['samples'].items():
            entry['samples_rechecked_by_verify_narrow'] = entry.get(
                'samples_rechecked_by_verify_narrow', True) and recheck_sample(pts, cols)
        results[str(cols)] = entry
        json.dump(results, open(out_path, 'w'), indent=1)
        print(f'width {cols} mode {mode}: a4 = {total} counts = {entry["counts"]} '
              f'nodes = {entry["nodes"]} seconds = {entry["seconds"]} status = {entry["status"]}',
              flush=True)


if __name__ == '__main__':
    main()
