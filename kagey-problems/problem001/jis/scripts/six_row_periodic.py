"""Six rows: periodic search for a blackout attaining the row bound m+9.

A blackout of m+9 points on 6 x m has exactly nine columns with two black points, whose row
pairs are the nine edges of a complete bipartite graph K_{3,3} on the rows, and one black
point in every other column (equality case of the row bound). This script tries the
periodic placements: doubles at columns 0, g, 2g, ..., 8g (width 8g+1) for g = 1..8, the
remaining columns black in row 0 (a boundary row), all 10 partitions of the rows into two
triples, all 9! orders of the edges, by depth-first search with pruning: a prefix of
columns whose rectangles already collide cannot be completed (restriction to a column
interval preserves validity). Row-5 singletons are covered by row reflection, which maps
partitions to partitions.

Rectangles come from verify_narrow.rectangles; the collision test is the same dictionary
test as verify_narrow.collision, maintained incrementally over the prefix. Every full
witness is rechecked from scratch with verify_narrow.collision and then put through the
finite-collar test (7 = 1 + floor(25/4) row-0 singleton columns prepended, appended, and
both), checked by verify_narrow.collision and by an independent side-vector enumerator.

Output: jis/data/six_row_periodic.json; witnesses as one-based (column, row).
"""
import json
import os
import sys
import time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, ROOT)

from verify_narrow import collision, mask, rectangles

ROWS = 6                                    # --rows 5 reruns the five-row calibration
COLLAR = 1 + (ROWS - 1) ** 2 // 4          # W_6 = 7
CAP_PER_SEARCH = 1800                       # seconds per (gap, partition)
MAX_STORED = 20
Q = (ROWS * ROWS) // 4                      # number of doubles (edges of K_{3,3}: 9)


def rectangles_by_sides(rows, cols):
    """Independent enumerator: corner plus two perpendicular side vectors; bitmasks."""
    pts = [(x, y) for y in range(rows) for x in range(cols)]
    inside = set(pts)
    vectors = [(a, b) for a in range(-(cols - 1), cols) for b in range(-(rows - 1), rows)
               if (a, b) != (0, 0)]
    found = set()
    for (x, y) in pts:
        for (a, b) in vectors:
            if (x + a, y + b) not in inside:
                continue
            for (c, d) in vectors:
                if a * c + b * d != 0:
                    continue
                if (x + c, y + d) not in inside or (x + a + c, y + b + d) not in inside:
                    continue
                found.add(mask(((x, y), (x + a, y + b), (x + c, y + d),
                                (x + a + c, y + b + d)), cols))
    return sorted(found)


def partitions():
    """Row partitions into parts of sizes floor(h/2) and ceil(h/2); each once."""
    out = []
    seen = set()
    for a in combinations(range(ROWS), ROWS // 2):
        b = tuple(r for r in range(ROWS) if r not in a)
        key = frozenset((a, b))
        if key not in seen:
            seen.add(key)
            out.append((a, b))
    return out


def board_points(order, g, cols):
    """Zero-based points of the periodic board with doubles `order` at 0, g, ..., 8g."""
    doubles = {k * g: order[k] for k in range(Q)}
    pts = set()
    for x in range(cols):
        if x in doubles:
            pts.add((x, doubles[x][0]))
            pts.add((x, doubles[x][1]))
        else:
            pts.add((x, 0))
    return pts


def one_based(pts):
    return sorted((x + 1, y + 1) for x, y in pts)


def search(g, part, rects_full, by_maxcol):
    """DFS over edge orders. Returns (witness list, nodes, pruned count, finished flag)."""
    A, B = part
    edges = [(a, b) for a in A for b in B]
    cols = (Q - 1) * g + 1
    seen = {}
    witnesses = []
    stats = {'nodes': 0, 'pruned': 0, 'finished': True}
    t0 = time.time()

    def add_range(black, lo, hi):
        """Add rectangles with maxcol in [lo, hi); return added keys or None on collision."""
        added = []
        for c in range(lo, hi):
            for r in by_maxcol[c]:
                vis = r & ~black
                if vis in seen:
                    for k in added:
                        del seen[k]
                    return None
                seen[vis] = r
                added.append(vis)
        return added

    def rec(depth, order, black, width):
        if time.time() - t0 > CAP_PER_SEARCH:
            stats['finished'] = False
            return
        if depth == Q:
            witnesses.append(tuple(order))
            return
        x = depth * g
        new_width = min((depth + 1) * g, cols)
        for e in edges:
            if e in order:
                continue
            stats['nodes'] += 1
            b2 = black | (1 << (e[0] * cols + x)) | (1 << (e[1] * cols + x))
            for xx in range(x + 1, new_width):
                b2 |= 1 << xx                      # row-0 singletons up to the next double
            added = add_range(b2, width, new_width)
            if added is None:
                stats['pruned'] += 1
                continue
            order.append(e)
            rec(depth + 1, order, b2, new_width)
            order.pop()
            for k in added:
                del seen[k]
            if not stats['finished']:
                return

    rec(0, [], 0, 0)
    return witnesses, stats, time.time() - t0


def collar_tests(pts, cols):
    """Finite-collar test on a zero-based point set of width `cols`, row-0 singletons."""
    out = {}
    for side in ('left', 'right', 'both'):
        left = COLLAR if side in ('left', 'both') else 0
        right = COLLAR if side in ('right', 'both') else 0
        w = cols + left + right
        shifted = {(x + left, y) for x, y in pts}
        shifted |= {(x, 0) for x in range(left)}
        shifted |= {(cols + left + x, 0) for x in range(right)}
        black = mask(shifted, w)
        r1 = rectangles(ROWS, w)
        r2 = rectangles_by_sides(ROWS, w)
        out[side] = {'width': w, 'rectangles': len(r1),
                     'enumerators_agree': sorted(r1) == r2,
                     'valid_by_verify_narrow': collision(r1, black) is None,
                     'valid_by_side_vectors': collision(r2, black) is None,
                     'points': one_based(shifted)}
    return out


def main():
    global ROWS, COLLAR, Q
    args = sys.argv[1:]
    if args[:1] == ['--rows']:
        ROWS = int(args[1])
        COLLAR = 1 + (ROWS - 1) ** 2 // 4
        Q = (ROWS * ROWS) // 4
        args = args[2:]
    gaps = [int(a) for a in args] or list(range(1, 9))
    results = []
    tag = '' if ROWS == 6 else f'_rows{ROWS}'
    for g in gaps:
        cols = (Q - 1) * g + 1
        rects = rectangles(ROWS, cols)
        by_maxcol = [[] for _ in range(cols)]
        for r in rects:
            mc = max(i % cols for i in range(r.bit_length()) if r >> i & 1)
            by_maxcol[mc].append(r)
        for part in partitions():
            wits, stats, dt = search(g, part, rects, by_maxcol)
            rec = {'gap': g, 'width': cols, 'partition': [list(part[0]), list(part[1])],
                   'rows': ROWS, 'rows_zero_based_in_partition': True, 'singleton_row': 1,
                   'rectangles': len(rects), 'nodes': stats['nodes'], 'pruned': stats['pruned'],
                   'finished': stats['finished'], 'seconds': round(dt, 2),
                   'witnesses_found': len(wits), 'witnesses': []}
            for order in wits[:MAX_STORED]:
                pts = board_points(order, g, cols)
                black = mask(pts, cols)
                w = {'edge_order_zero_based_rows': [list(e) for e in order],
                     'size': len(pts), 'points': one_based(pts),
                     'valid_by_verify_narrow': collision(rects, black) is None}
                if w['valid_by_verify_narrow']:
                    w['collar'] = collar_tests(pts, cols)
                rec['witnesses'].append(w)
            print(json.dumps({k: v for k, v in rec.items() if k != 'witnesses'}), flush=True)
            for w in rec['witnesses']:
                print('  witness', w['edge_order_zero_based_rows'], 'collar:',
                      {s: (c['valid_by_verify_narrow'], c['valid_by_side_vectors'])
                       for s, c in w.get('collar', {}).items()}, flush=True)
            results.append(rec)
            with open(os.path.join(ROOT, 'jis', 'data', f'six_row_periodic{tag}.json'), 'w') as fh:
                json.dump(results, fh, indent=1)


if __name__ == '__main__':
    main()
