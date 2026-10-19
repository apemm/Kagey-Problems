"""Write the unsatisfiable SAT instances of Section 9 as DIMACS files, for proof checking.

These are the instances behind f(5,6) < 12, f(5,7) < 13, f(6,6) < 13, f(6,7) < 14, f(6,8) < 16, f(7,7) < 15, f(7,8) < 17, and the
six-row partition instances of the six-row theorem, part (a) (no valid blackout of m+9 points on the 6 x m
grid with the equality structure, for one of the ten row partitions). Each file is written
from the encodings the paper describes, with the cardinality constraint written out here as
an explicit sequential counter (Sinz 2005), so that no clause comes from a library.

Variables (one-based, as in DIMACS). The point (x, y), zero-based column x and row y, is the
variable y*m + x + 1. Coordinates in the reports are one-based (column, row), (1,1) top left.

Cell instances (encoding A). One clause "not all black" for each inclusion-minimal symmetric
difference of two rectangles (rectangles from verify_narrow.rectangles), then "at least k
points" as "at most n-k of the negated point literals" by the sequential counter below, with
auxiliary variables numbered from n+1. Clauses are written sorted and without repeats.

Split instances. On 6 x 8, 7 x 7 and 7 x 8 the instance is cut by the content of the first
column, as in table_counts_sat.py --split, so that each proof stays small enough to check:
part p (p = 0 .. 2^h - 1) adds the unit clause +v or -v for the point (0, y), positive exactly
when bit y of p is set. The 2^h parts cover every assignment of the first column, so the
base instance is unsatisfiable when every part is.
Only the base CNF and the list of parts go to the repository; each part is the base plus its
units, and --parts writes them out.

Six-row instances (structured encoder A of six_row_structured_sat.py). For the partition of
the rows {0..5} into the triple A that contains row 0 and its complement B, the edges are the
pairs (min(a,b), max(a,b)) listed for a in A, then b in B. Column x has 15 type variables,
n + 15x + j + 1 for j = 0..14: types 0..5 are the single rows, types 6..14 the edges in the
order above. Clauses: each column has exactly one type (one clause and pairwise exclusions);
a type puts its rows black and only those (a black point needs a type holding its row); each
edge type is used in exactly one column (one clause and pairwise exclusions); for every pair
of rectangles that share a corner, at least one of them tilted, whose symmetric difference
could be all black under the structure, the clause "not all black"; for each tilted
rectangle whose four corners could be black, an indicator f with "all four corners black
implies f", the indicators numbered from n + 15m + 1 in the order of the sorted corner
variables; and at most one indicator true, by the sequential counter with K = 1.

The sequential counter for "at most K of the literals l_1..l_r" uses s(i,j) for i = 1..r-1,
j = 1..K, numbered top + (i-1)K + j:
  (-l_1 s(1,1)), (-s(1,j)) for j = 2..K,
  for 1 < i < r: (-l_i s(i,1)), (-s(i-1,1) s(i,1)),
                 (-l_i -s(i-1,j-1) s(i,j)), (-s(i-1,j) s(i,j)) for j = 2..K,
                 (-l_i -s(i-1,K)),
  (-l_r -s(r-1,K)).
Setting s(i,j) true exactly when at least j of l_1..l_i are true satisfies every clause when at
most K of the l_i are true.

Usage: python unsat_export_cnf.py OUTDIR [--parts]
Writes OUTDIR/<name>.cnf for every instance, OUTDIR/splits.json (the parts of each split
instance and their units) and OUTDIR/manifest.json (sizes and SHA-256 of the clause sets).
"""
import hashlib
import json
import os
import sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, ROOT)

from verify_narrow import rectangles  # noqa: E402

CELLS = [(5, 6, 12, False), (5, 7, 13, False), (6, 6, 13, False), (6, 7, 14, False), (6, 8, 16, True), (7, 7, 15, True), (7, 8, 17, True)]
SIX_ROW_WIDTHS = range(8, 15)


def bits(x):
    return [i for i in range(x.bit_length()) if x >> i & 1]


def at_most(lits, K, top):
    """Sequential counter for "at most K of lits"; returns (clauses, new top)."""
    r = len(lits)
    if K >= r:
        return [], top
    if K == 0:
        return [[-l] for l in lits], top

    def s(i, j):
        return top + (i - 1) * K + j

    out = [[-lits[0], s(1, 1)]] + [[-s(1, j)] for j in range(2, K + 1)]
    for i in range(2, r):
        li = lits[i - 1]
        out.append([-li, s(i, 1)])
        out.append([-s(i - 1, 1), s(i, 1)])
        for j in range(2, K + 1):
            out.append([-li, -s(i - 1, j - 1), s(i, j)])
            out.append([-s(i - 1, j), s(i, j)])
        out.append([-li, -s(i - 1, K)])
    out.append([-lits[r - 1], -s(r - 1, K)])
    return out, top + (r - 1) * K


def canon(clauses):
    """Sorted clauses without repeats, each sorted by variable then sign."""
    return sorted({tuple(sorted(set(c), key=lambda l: (abs(l), l))) for c in clauses})


def clause_hash(clauses):
    text = '\n'.join(' '.join(map(str, c)) for c in canon(clauses))
    return hashlib.sha256(text.encode()).hexdigest()


def write_dimacs(path, nvars, clauses, comments):
    cl = canon(clauses)
    with open(path, 'w', newline='\n') as fh:
        for c in comments:
            fh.write(f'c {c}\n')
        fh.write(f'p cnf {nvars} {len(cl)}\n')
        for c in cl:
            fh.write(' '.join(map(str, c)) + ' 0\n')
    return cl


# ------------------------------------------------------------------ cell instances

def minimal_differences(rects):
    diffs = sorted({a ^ b for a, b in combinations(rects, 2)}, key=lambda d: d.bit_count())
    kept = []
    for d in diffs:
        if not any(k & d == k for k in kept):
            kept.append(d)
    return kept


def cell_cnf(h, m, k):
    n = h * m
    kept = minimal_differences(rectangles(h, m))
    clauses = [[-(i + 1) for i in bits(d)] for d in kept]
    card, top = at_most([-(i + 1) for i in range(n)], n - k, n)
    return clauses + card, top, {'minimal_differences': len(kept)}


def part_units(h, m, p):
    return [[(y * m + 1) if p >> y & 1 else -(y * m + 1)] for y in range(h)]


# ------------------------------------------------------------------ six-row instances

def six_partitions():
    out = []
    for A in combinations(range(6), 3):
        if 0 in A:
            out.append((A, tuple(r for r in range(6) if r not in A)))
    return out


def is_axis(r, m):
    return len({i % m for i in bits(r)}) == 2 and len({i // m for i in bits(r)}) == 2


def feasible(d, m, edge_set):
    rows_in_col = {}
    for i in bits(d):
        rows_in_col.setdefault(i % m, []).append(i // m)
    used = set()
    for rs in rows_in_col.values():
        if len(rs) >= 3:
            return False
        if len(rs) == 2:
            e = (min(rs), max(rs))
            if e not in edge_set or e in used:
                return False
            used.add(e)
    return True


def six_cnf(m, part):
    A, B = part
    edges = [(min(a, b), max(a, b)) for a in A for b in B]
    edge_set = set(edges)
    n = 6 * m
    types = [(r,) for r in range(6)] + edges

    def t(x, j):
        return n + 15 * x + j + 1

    cl = []
    for x in range(m):
        cl.append([t(x, j) for j in range(15)])
        cl += [[-t(x, i), -t(x, j)] for i, j in combinations(range(15), 2)]
        for r in range(6):
            holders = [t(x, j) for j, ty in enumerate(types) if r in ty]
            cl += [[-hv, r * m + x + 1] for hv in holders]
            cl.append([-(r * m + x + 1)] + holders)
    for j in range(6, 15):
        cl.append([t(x, j) for x in range(m)])
        cl += [[-t(x, j), -t(y, j)] for x, y in combinations(range(m), 2)]
    rects = rectangles(6, m)
    tilted = {r for r in rects if not is_axis(r, m)}
    by_corner = {}
    for r in rects:
        for i in bits(r):
            by_corner.setdefault(i, set()).add(r)
    pairs = set()
    for group in by_corner.values():
        for a, b in combinations(sorted(group), 2):
            if a in tilted or b in tilted:
                pairs.add((a, b))
    npair = 0
    for a, b in pairs:
        d = a ^ b
        if feasible(d, m, edge_set):
            cl.append([-(i + 1) for i in bits(d)])
            npair += 1
    full = sorted(tuple(i + 1 for i in bits(r)) for r in tilted if feasible(r, m, edge_set))
    top = n + 15 * m
    ind = []
    for corners in full:
        top += 1
        ind.append(top)
        cl.append([-v for v in corners] + [top])
    amo, top = at_most(ind, 1, top)
    cl += amo
    return cl, top, {'rectangles': len(rects), 'tilted': len(tilted),
                     'pair_clauses_with_repeats': npair, 'indicators': len(ind)}


# ------------------------------------------------------------------ driver

def instances():
    """Yield (name, nvars, clauses, info) for every base instance."""
    for h, m, k, split in CELLS:
        cl, nv, info = cell_cnf(h, m, k)
        info.update(kind='cell', rows=h, cols=m, at_least=k, split=split,
                    claim=f'no valid blackout of {k} points on the {h} x {m} grid, so f({h},{m}) < {k}')
        yield f'cell_{h}x{m}_k{k}', nv, cl, info
    for m in SIX_ROW_WIDTHS:
        for idx, part in enumerate(six_partitions()):
            cl, nv, info = six_cnf(m, part)
            one = [[r + 1 for r in part[0]], [r + 1 for r in part[1]]]
            info.update(kind='six_row', rows=6, cols=m, partition_one_based_rows=one,
                        claim=f'no valid blackout of {m + 9} points on the 6 x {m} grid whose '
                              f'doubles carry K_3,3 for rows {one[0]} | {one[1]}')
            yield f'six_w{m}_p{idx}', nv, cl, info


def main():
    out = sys.argv[1]
    write_parts = '--parts' in sys.argv
    os.makedirs(out, exist_ok=True)
    manifest, splits = [], {}
    for name, nv, cl, info in instances():
        cc = write_dimacs(os.path.join(out, name + '.cnf'), nv, cl,
                          [f'{name}: {info["claim"]}', 'written by unsat_export_cnf.py'])
        rec = {'name': name, 'variables': nv, 'clauses': len(cc),
               'clause_set_sha256': clause_hash(cc), **info}
        if info.get('split'):
            h, m = info['rows'], info['cols']
            parts = []
            for p in range(2 ** h):
                units = part_units(h, m, p)
                pc = cc + [tuple(u) for u in units]
                pname = f'{name}_part{p:03d}'
                parts.append({'name': pname, 'units': [u[0] for u in units],
                              'clause_set_sha256': clause_hash(pc)})
                if write_parts:
                    write_dimacs(os.path.join(out, pname + '.cnf'), nv, pc,
                                 [f'{pname}: part {p} of {name}, first column fixed',
                                  'written by unsat_export_cnf.py'])
            splits[name] = {'split': 'by the content of the first column',
                            'first_column_variables': [y * m + 1 for y in range(h)],
                            'parts': parts}
        manifest.append(rec)
        print(json.dumps(rec), flush=True)
    with open(os.path.join(out, 'manifest.json'), 'w') as fh:
        json.dump(manifest, fh, indent=1)
    with open(os.path.join(out, 'splits.json'), 'w') as fh:
        json.dump(splits, fh, indent=1)


if __name__ == '__main__':
    main()
