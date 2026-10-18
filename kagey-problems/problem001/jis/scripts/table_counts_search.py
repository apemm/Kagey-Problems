"""Count the maximum blackouts a_h(m) of small grids by a column-by-column search.

This is the second route for the missing entries of A399580, written without the SAT code and
without verify_narrow. It uses only the standard library.

Rectangles. For every ordered pair of grid points P, Q we take the primitive vector w
perpendicular to Q - P and every nonzero multiple t*w that keeps P + t*w and Q + t*w on the grid.
The four corners give one rectangle, and duplicates are removed by their corner sets.

Search. Let h be the smaller side, so a column is a subset of h rows. Columns are chosen from
left to right. A rectangle is decided as soon as its last column is chosen, and its visible
corners are compared with those of every rectangle decided before it. Two equal visible sets
mean the blackout is not valid, and the branch is cut. When every column is chosen, all
rectangles are decided, so a leaf is a valid blackout.

Pruning. A valid blackout stays valid on any block of consecutive columns. So after c columns
with p points, the other m - c columns hold at most f(h, m - c) points, and we need
p >= k - f(h, m - c). The values of f on narrower grids are the computed values of the paper,
listed in F below. Every leaf must have exactly k points.

Usage: python table_counts_search.py 5x6@11 5x7@12 ...   (results go to --out, default
jis/data/table_counts_search.json). The cap is checked at every node. With --split N the cell
is cut into one part for each possible first column (or first d columns, with --depth d), the
parts run on N processes, and each part has its own cap. The count is exact only when every part finishes.
"""
import hashlib
import json
import os
import sys
import time
from math import gcd

CAP_SECONDS = 1800

# f(h, c) for h <= c <= 8 from the paper's table (f(h,c) = f(c,h)); f(h,0) = 0 and f(h,1) = h.
F = {(2, 2): 4, (2, 3): 4, (2, 4): 5, (2, 5): 6, (2, 6): 7, (2, 7): 8, (2, 8): 9,
     (3, 3): 5, (3, 4): 6, (3, 5): 7, (3, 6): 8, (3, 7): 9, (3, 8): 10,
     (4, 4): 7, (4, 5): 8, (4, 6): 10, (4, 7): 11, (4, 8): 12,
     (5, 5): 10, (5, 6): 11, (5, 7): 12, (5, 8): 14,
     (6, 6): 12, (6, 7): 13, (6, 8): 15, (7, 7): 14}


def f_known(h, c):
    if c == 0:
        return 0
    if c == 1 or h == 1:
        return max(h, c) if min(h, c) == 1 else None
    return F.get((min(h, c), max(h, c)))


def all_rectangles(h, m):
    """Corner sets, as sorted tuples of (column, row), zero-based."""
    pts = [(x, y) for x in range(m) for y in range(h)]
    found = set()
    for (px, py) in pts:
        for (qx, qy) in pts:
            if (qx, qy) <= (px, py):
                continue
            dx, dy = qx - px, qy - py
            g = gcd(dx, dy)
            wx, wy = -dy // g, dx // g
            for t in range(-max(h, m), max(h, m) + 1):
                if t == 0:
                    continue
                a = (px + t * wx, py + t * wy)
                b = (qx + t * wx, qy + t * wy)
                if 0 <= a[0] < m and 0 <= a[1] < h and 0 <= b[0] < m and 0 <= b[1] < h:
                    found.add(tuple(sorted(((px, py), (qx, qy), a, b))))
    return sorted(found)


def count(h, m, k, cap=CAP_SECONDS, keep=20, prefix=()):
    if h > m:
        raise ValueError('give the smaller side first')
    rects = all_rectangles(h, m)
    bit = lambda x, y: x * h + y
    by_last = [[] for _ in range(m)]
    for r in rects:
        by_last[max(x for x, _ in r)].append(sum(1 << bit(x, y) for x, y in r))
    need = [0] + [k - f_known(h, m - c) for c in range(1, m + 1)]
    subsets = sorted(range(1 << h), key=lambda s: -bin(s).count('1'))
    seen = set()
    hits = []
    nodes = [0]
    t0 = time.time()

    class Cap(Exception):
        pass

    def go(c, black, p):
        nodes[0] += 1
        if nodes[0] & 0xFFF == 0 and time.time() - t0 > cap:
            raise Cap
        if c == m:
            if p == k:
                hits.append(black)
            return
        for s in (subsets if c >= len(prefix) else [prefix[c]]):
            q = p + bin(s).count('1')
            if q > k or q < need[c + 1]:
                continue
            nb = black | (s << (c * h))
            added = []
            ok = True
            for r in by_last[c]:
                v = r & ~nb
                if v in seen:
                    ok = False
                    break
                seen.add(v)
                added.append(v)
            if ok:
                go(c + 1, nb, q)
            for v in added:
                seen.discard(v)

    status = 'exact'
    try:
        go(0, 0, 0)
    except Cap:
        status = 'unresolved'
    dt = time.time() - t0

    def one_based(b):
        return sorted((i // h + 1, i % h + 1) for i in range(h * m) if b >> i & 1)

    models = sorted(one_based(b) for b in hits)
    return {'grid': f'{h}x{m}', 'rows': h, 'cols': m, 'size': k, 'rectangles': len(rects),
            'prefix': list(prefix), 'status': status, 'count': len(hits) if status == 'exact' else None,
            'found_so_far': len(hits), 'nodes': nodes[0], 'seconds': round(dt, 2),
            'coordinates': 'one-based (column,row), (1,1) top-left',
            'models_sha256': digest(models), 'first_hits': models[:keep], 'all': models}


def digest(models):
    """SHA-256 of the sorted list of models, each a sorted list of one-based (column,row)."""
    text = json.dumps(sorted([list(p) for p in mo] for mo in models))
    return hashlib.sha256(text.encode()).hexdigest()


def _part(job):
    h, m, k, prefix = job
    return count(h, m, k, prefix=prefix)


def count_split(h, m, k, workers, depth=1):
    from itertools import product
    from multiprocessing import Pool
    jobs = [(h, m, k, pre) for pre in product(range(1 << h), repeat=depth)
            if sum(bin(s).count('1') for s in pre) <= k]
    with Pool(workers) as pool:
        parts = pool.map(_part, jobs, chunksize=1)
    models = sorted(mo for p in parts for mo in p['all'])
    exact = all(p['status'] == 'exact' for p in parts)
    return {'grid': f'{h}x{m}', 'rows': h, 'cols': m, 'size': k,
            'rectangles': parts[0]['rectangles'], 'split': f'by the first {depth} columns',
            'parts': len(parts), 'parts_unresolved': [p['prefix'] for p in parts
                                                      if p['status'] != 'exact'],
            'status': 'exact' if exact else 'unresolved',
            'count': len(models) if exact else None, 'found_so_far': len(models),
            'nodes': sum(p['nodes'] for p in parts),
            'seconds_max_part': max(p['seconds'] for p in parts),
            'seconds_total': round(sum(p['seconds'] for p in parts), 2),
            'coordinates': 'one-based (column,row), (1,1) top-left',
            'models_sha256': digest(models), 'first_hits': models[:20], 'all': models}


def main():
    args = sys.argv[1:]
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'data',
                       'table_counts_search.json')
    if '--out' in args:
        i = args.index('--out')
        out = args[i + 1]
        del args[i:i + 2]
    workers = 0
    if '--split' in args:
        i = args.index('--split')
        workers = int(args[i + 1])
        del args[i:i + 2]
    depth = 1
    if '--depth' in args:
        i = args.index('--depth')
        depth = int(args[i + 1])
        del args[i:i + 2]
    results = []
    for cell in args:
        grid, _, k = cell.partition('@')
        h, m = map(int, grid.split('x'))
        rec = (count_split(h, m, int(k), workers, depth) if workers
               else count(h, m, int(k)))
        rec.pop('all')
        print(json.dumps({x: rec[x] for x in rec if x != 'first_hits'}), flush=True)
        results.append(rec)
        with open(out, 'w') as fh:
            json.dump(results, fh, indent=1)


if __name__ == '__main__':
    main()
