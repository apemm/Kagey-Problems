"""Exact SAT search for equality boards of a given height and row partition.

An equality board has one double column for every pair of the complete bipartite
graph between two row classes A and B, and a singleton in every other column.
The geometric clauses are the positive forbidden supports of
../full_problem_push/compact_equality_sat.md, generated here for any height from
side-vector templates and translated along the board. UNSAT therefore means
that no equality board with the given partition and width exists.

Every board that the solver returns is checked afterwards with rectlib.check_board,
which shares no code with this encoder.
"""
from itertools import combinations
from math import gcd
from pathlib import Path
import sys, time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'full_problem_push' / '.runtime'))
sys.path.insert(0, str(HERE))


def tilted_shapes(h):
    out = []
    for p in range(1, h):
        for q in range(1, h):
            if gcd(p, q) != 1:
                continue
            for s in range(1, h):
                if s * q > h - 1:
                    break
                for t in range(1, h):
                    if s * q + t * p > h - 1:
                        break
                    u = (s * p, s * q); v = (-t * q, t * p)
                    pts = [(0, 0), u, v, (u[0] + v[0], u[1] + v[1])]
                    mc = min(c for c, _ in pts)
                    out.append(tuple((c - mc, r) for c, r in pts))
    return out


def norm(cells, extent):
    """Shift a support so that the left edge of its extent is column 0.

    The extent is the set of all columns of the rectangles that define the
    support. A support applies at a position only when its whole extent lies
    on the board, because the shared or removed corners must be grid cells.
    Returns (cells, last column of the extent).
    """
    lo = min(extent); hi = max(extent)
    return frozenset((c - lo, r) for c, r in cells), hi - lo


class Geometry:
    """Partition-independent raw data: placed tilted rectangles and pair supports."""

    def __init__(self, h):
        self.h = h
        shapes = tilted_shapes(h)
        self.span = max(max(c for c, _ in s) for s in shapes) + 1
        self.placed = []
        for s in shapes:
            top = max(r for _, r in s)
            for r0 in range(h - top):
                self.placed.append(frozenset((c, r + r0) for c, r in s))
        pair = set()
        for R in self.placed:
            for X in R:
                for s in shapes:
                    for k in s:
                        dc = X[0] - k[0]; dr = X[1] - k[1]
                        T = frozenset((c + dc, r + dr) for c, r in s)
                        if T == R or any(r < 0 or r >= h for _, r in T):
                            continue
                        pair.add(norm(R ^ T, [c for c, _ in R | T]))
        self.pair = pair


def supports(geo, A):
    """Forbidden supports as (cells, extent width - 1), left edge of the extent at column 0.

    Supports that contain a smaller forbidden support whose extent is its own
    column range are dropped; this keeps the clause set exact.
    """
    h = geo.h
    cls = [1 if r in A else 0 for r in range(h)]

    def feasible(D):
        cols = {}
        for c, r in D:
            cols.setdefault(c, []).append(r)
        used = set()
        for rows in cols.values():
            if len(rows) > 2:
                return False
            if len(rows) == 2:
                if cls[rows[0]] == cls[rows[1]]:
                    return False
                e = frozenset(rows)
                if e in used:
                    return False
                used.add(e)
        return True

    raw = set()
    for R in geo.placed:
        ext = [c for c, _ in R]
        raw.add(norm(R, ext))
        for P in R:
            c, r = P
            for s in range(h):
                if cls[s] != cls[r]:
                    raw.add(norm((R - {P}) | {(c, s)}, ext))
        for P, Q in combinations(sorted(R), 2):
            (c, r), (d, s) = P, Q
            rest = R - {P, Q}
            if c == d:
                if cls[r] != cls[s]:
                    raw.add(norm(rest, ext))
            elif r == s:
                for row in range(h):
                    raw.add(norm(rest | {(c, row), (d, row)}, ext))
            else:
                raw.add(norm(rest | {(c, s), (d, r)}, ext))
    raw |= geo.pair
    by = {}
    for D, hi in raw:
        if feasible(D):
            by.setdefault(len(D), set()).add((D, hi))
    tight = {}   # self-contained supports, keyed by size, normalized to their own left column
    out = []
    for k in sorted(by):
        keep = []
        for D, hi in by[k]:
            cells = sorted(D)
            red = False
            for j in tight:
                for sub in combinations(cells, j):
                    lo = min(c for c, _ in sub)
                    if frozenset((c - lo, r) for c, r in sub) in tight[j]:
                        red = True; break
                if red:
                    break
            if not red:
                keep.append((D, hi))
        tight[k] = set()
        for D, hi in keep:
            cs = [c for c, _ in D]
            if min(cs) == 0 and max(cs) == hi:
                tight[k].add(D)
        out.extend(keep)
    return out


def encode(h, w, A, sup, label_width=None, fixed_tail=None, anchor=True):
    """CNF for width w. Doubles are allowed only in the first label_width columns.
    fixed_tail = (first_column, row) fixes that singleton row from first_column on."""
    A = set(A)
    Bc = [r for r in range(h) if r not in A]
    edges = [(a, b) for a in sorted(A) for b in Bc]
    lw = w if label_width is None else label_width
    x = lambda c, r: c * h + r + 1
    nv = w * h
    y = {}
    cl = []
    for c in range(w):
        cl.append([x(c, r) for r in range(h)])
        for r, s in combinations(range(h), 2):
            if (r in A) == (s in A) or c >= lw:
                cl.append([-x(c, r), -x(c, s)])
    for j, (a, b) in enumerate(edges):
        vs = []
        for c in range(lw):
            nv += 1; y[c, j] = nv; vs.append(nv)
            cl.append([-nv, x(c, a)]); cl.append([-nv, x(c, b)]); cl.append([nv, -x(c, a), -x(c, b)])
        cl.append(vs)
        cl.extend([-u, -v] for u, v in combinations(vs, 2))
    if anchor:
        cl.append([y[c, 0] for c in range((lw + 1) // 2)])
    if fixed_tail is not None:
        c0, row = fixed_tail
        for c in range(c0, w):
            cl.append([x(c, row)])
    for D, sp in sup:
        lits = sorted(D)
        for off in range(w - sp):
            cl.append([-x(c + off, r) for c, r in lits])
    return cl, nv


def solve(clauses, cap, chunk=4000):
    from pysat.solvers import Solver
    t0 = time.monotonic()
    with Solver(name='cadical195', bootstrap_with=clauses) as s:
        res = None
        while True:
            s.conf_budget(chunk)
            res = s.solve_limited()
            if res is not None or time.monotonic() - t0 > cap:
                break
        model = s.get_model() if res else None
        stats = s.accum_stats()
    status = 'SAT' if res else ('UNSAT' if res is False else 'unknown')
    return status, model, time.monotonic() - t0, stats


def board_from_model(h, w, model):
    pos = set(v for v in model if 0 < v <= w * h)
    return [[r + 1 for r in range(h) if c * h + r + 1 in pos] for c in range(w)]


def word(cols):
    return ','.join('.'.join(str(r) for r in c) for c in cols)


def partitions(h):
    """Balanced row partitions (smaller side A), one per vertical reflection class."""
    k = h // 2
    full = frozenset(range(h))
    seen = set(); out = []

    def canon(fa):
        if h % 2 == 0 and 0 not in fa:
            fa = full - fa  # A and its complement give the same graph
        return tuple(sorted(fa))

    for A in combinations(range(h), k):
        fa = frozenset(A)
        key = min(canon(fa), canon(frozenset(h - 1 - r for r in fa)))
        if key not in seen:
            seen.add(key); out.append(key)
    return out
