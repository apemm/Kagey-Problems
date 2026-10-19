"""Second, separately written generator for the CNF files of unsat_export_cnf.py.

It shares no code with unsat_export_cnf.py or verify_narrow.py. Rectangles come from right-angle
triples: for points P, Q, R of the grid with P - Q perpendicular to R - Q (both nonzero), the
fourth corner is P + R - Q, kept when it lies on the grid. The minimal differences are found by
testing every proper subset of each difference for membership, instead of by comparing
differences pairwise. The sequential counter and the six-row encoding are rebuilt from the
description in the docstring of unsat_export_cnf.py, with the same variable numbering.

For each instance the clause set built here is compared with the clause set read from the
DIMACS file (clauses as sets of literals, the formula as a set of clauses). For split instances
it checks that every part file is the base clause set plus exactly the units of its part and
that the units of the parts run over all 2^h sign patterns of the first column, each once. For
the six-row instances it checks that the ten files of a width are the ten splits of the rows
into two triples.

Usage: python unsat_cnf_crosscheck.py CNFDIR OUT.json
"""
import hashlib
import json
import os
import sys
from itertools import combinations, product


def grid_points(h, m):
    return [(x, y) for y in range(h) for x in range(m)]


def rects_by_triples(h, m):
    pts = grid_points(h, m)
    on = set(pts)
    out = set()
    for q in pts:
        for p in pts:
            if p == q:
                continue
            ux, uy = p[0] - q[0], p[1] - q[1]
            for r in pts:
                if r == q or r == p:
                    continue
                vx, vy = r[0] - q[0], r[1] - q[1]
                if ux * vx + uy * vy:
                    continue
                s = (p[0] + vx, p[1] + vy)
                if s in on:
                    out.add(frozenset((p, q, r, s)))
    return out


def v(pt, m):
    return pt[1] * m + pt[0] + 1


def seq_counter(lits, K, top):
    """At most K of lits (Sinz), aux s(i,j) = top + (i-1)K + j; returns (clauses, top)."""
    r = len(lits)
    if K >= r:
        return [], top
    reg = [[top + (i - 1) * K + j for j in range(1, K + 1)] for i in range(1, r)]
    cls = []
    for i in range(1, r + 1):
        li = lits[i - 1]
        if i < r:
            cur = reg[i - 1]
            cls.append((-li, cur[0]))
            if i == 1:
                cls += [(-cur[j],) for j in range(1, K)]
            else:
                prev = reg[i - 2]
                cls.append((-prev[0], cur[0]))
                for j in range(1, K):
                    cls.append((-li, -prev[j - 1], cur[j]))
                    cls.append((-prev[j], cur[j]))
        if i > 1:
            cls.append((-li, -reg[i - 2][K - 1]))
    return cls, top + (r - 1) * K


def norm(cls):
    return frozenset(frozenset(c) for c in cls)


def digest(clause_set):
    text = '\n'.join(sorted(' '.join(map(str, sorted(c))) for c in clause_set))
    return hashlib.sha256(text.encode()).hexdigest()


def read_dimacs(path):
    nv = nc = None
    cls, cur = [], []
    with open(path) as fh:
        for line in fh:
            if line.startswith('c'):
                continue
            if line.startswith('p'):
                _, _, a, b = line.split()
                nv, nc = int(a), int(b)
                continue
            for t in line.split():
                t = int(t)
                if t == 0:
                    cls.append(cur)
                    cur = []
                else:
                    cur.append(t)
    assert not cur and nc == len(cls)
    return nv, cls


def cell_clauses(h, m, k):
    rects = rects_by_triples(h, m)
    diffs = {a ^ b for a, b in combinations(rects, 2)}
    minimal = []
    for d in diffs:
        items = sorted(d)
        proper = any(frozenset(sub) in diffs
                     for size in range(2, len(items))
                     for sub in combinations(items, size))
        if not proper:
            minimal.append(d)
    n = h * m
    cls = [tuple(-v(p, m) for p in d) for d in minimal]
    card, top = seq_counter([-i for i in range(1, n + 1)], n - k, n)
    return cls + card, top, len(rects), len(minimal)


def six_clauses(m, A, B, rects, pairdiffs):
    n = 6 * m
    edges = [(min(a, b), max(a, b)) for a in A for b in B]
    eset = set(edges)
    kinds = [{r} for r in range(6)] + [set(e) for e in edges]

    def t(x, j):
        return n + 15 * x + j + 1

    def can_be_black(d):
        per = {}
        for (x, y) in d:
            per.setdefault(x, set()).add(y)
        seen = []
        for ys in per.values():
            if len(ys) > 2:
                return False
            if len(ys) == 2:
                e = tuple(sorted(ys))
                if e not in eset:
                    return False
                seen.append(e)
        return len(seen) == len(set(seen))

    cls = []
    for x in range(m):
        cls.append(tuple(t(x, j) for j in range(15)))
        for i in range(15):
            for j in range(i + 1, 15):
                cls.append((-t(x, i), -t(x, j)))
        for y in range(6):
            hold = [t(x, j) for j in range(15) if y in kinds[j]]
            for hv in hold:
                cls.append((-hv, v((x, y), m)))
            cls.append(tuple([-v((x, y), m)] + hold))
    for j in range(6, 15):
        cls.append(tuple(t(x, j) for x in range(m)))
        for x in range(m):
            for y in range(x + 1, m):
                cls.append((-t(x, j), -t(y, j)))
    for d in pairdiffs:
        if can_be_black(d):
            cls.append(tuple(-v(p, m) for p in d))

    def tilted(r):
        return len({p[0] for p in r}) != 2 or len({p[1] for p in r}) != 2

    full = sorted(tuple(sorted(v(p, m) for p in r)) for r in rects
                  if tilted(r) and can_be_black(r))
    top = n + 15 * m
    ind = list(range(top + 1, top + 1 + len(full)))
    for corners, f in zip(full, ind):
        cls.append(tuple([-c for c in corners] + [f]))
    amo, top = seq_counter(ind, 1, top + len(full))
    return cls + amo, top


def main():
    cnfdir, outpath = sys.argv[1], sys.argv[2]
    report = {'instances': [], 'splits': [], 'six_row_partitions': []}
    ok_all = True

    def compare(name, nv, cls):
        nonlocal ok_all
        fnv, fcls = read_dimacs(os.path.join(cnfdir, name + '.cnf'))
        a, b = norm(cls), norm(fcls)
        same = a == b and nv == fnv
        ok_all &= same
        rec = {'name': name, 'identical_clause_sets': same, 'variables_here': nv,
               'variables_file': fnv, 'clauses_here': len(a), 'clauses_file': len(b),
               'clause_set_sha256_here': digest(a), 'clause_set_sha256_file': digest(b)}
        report['instances'].append(rec)
        print(json.dumps(rec), flush=True)
        return b

    for h, m, k in ((5, 6, 12), (5, 7, 13), (6, 6, 13), (6, 7, 14), (6, 8, 16), (7, 7, 15), (7, 8, 17)):
        cls, nv, nr, nmin = cell_clauses(h, m, k)
        name = f'cell_{h}x{m}_k{k}'
        base = compare(name, nv, cls)
        report['instances'][-1].update(rectangles=nr, minimal_differences=nmin)
        if (h, m) in ((5, 6), (5, 7), (6, 6), (6, 7)):
            continue
        col = [v((0, y), m) for y in range(h)]
        patterns = set()
        parts_ok = True
        for p in range(2 ** h):
            pname = f'{name}_part{p:03d}'
            pnv, pcls = read_dimacs(os.path.join(cnfdir, pname + '.cnf'))
            ps = norm(pcls)
            units = ps - base
            signs = []
            for c in units:
                (lit,) = tuple(c) if len(c) == 1 else (None,)
                signs.append(lit)
            good = (pnv == nv and base <= ps and len(units) == h and None not in signs
                    and sorted(abs(l) for l in signs) == col)
            if good:
                patterns.add(tuple(sorted(signs, key=abs)))
            parts_ok &= good
        all_patterns = {tuple(c if s else -c for c, s in zip(col, bits))
                        for bits in product((False, True), repeat=h)}
        cover = parts_ok and patterns == all_patterns
        ok_all &= cover
        rec = {'name': name, 'parts': 2 ** h, 'every_part_is_base_plus_units': parts_ok,
               'distinct_patterns': len(patterns), 'patterns_cover_all': cover}
        report['splits'].append(rec)
        print(json.dumps(rec), flush=True)

    for m in range(8, 15):
        rects = rects_by_triples(6, m)
        pairdiffs = set()
        rl = list(rects)
        for i in range(len(rl)):
            for j in range(i + 1, len(rl)):
                a, b = rl[i], rl[j]
                axis_a = len({p[0] for p in a}) == 2 and len({p[1] for p in a}) == 2
                axis_b = len({p[0] for p in b}) == 2 and len({p[1] for p in b}) == 2
                if a & b and not (axis_a and axis_b):
                    pairdiffs.add(a ^ b)
        seen_parts = set()
        for idx in range(10):
            name = f'six_w{m}_p{idx}'
            with open(os.path.join(cnfdir, name + '.cnf')) as fh:
                head = fh.readline()
            A = [int(c) - 1 for c in head.split('rows [')[1].split(']')[0].split(',')]
            B = [r for r in range(6) if r not in A]
            seen_parts.add(frozenset((frozenset(A), frozenset(B))))
            cls, nv = six_clauses(m, sorted(A), B, rects, pairdiffs)
            compare(name, nv, cls)
        all_parts = {frozenset((frozenset(T), frozenset(set(range(6)) - set(T))))
                     for T in combinations(range(6), 3)}
        good = seen_parts == all_parts and len(all_parts) == 10
        ok_all &= good
        rec = {'width': m, 'partitions': len(seen_parts), 'all_ten_splits_present': good}
        report['six_row_partitions'].append(rec)
        print(json.dumps(rec), flush=True)

    report['all_agree'] = ok_all
    with open(outpath, 'w') as fh:
        json.dump(report, fh, indent=1)
    print('all agree:', ok_all)


if __name__ == '__main__':
    main()
