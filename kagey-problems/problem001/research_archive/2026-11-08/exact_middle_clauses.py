"""Exhaustive fixed-order middle-cell constraints, using rectangle differences.

Standard library only. No claim about forbidden geometric families is built in.
Columns are 0..4(q-1), with a double at 4j and gap 1,x,h.
A constraint is a forbidden partial assignment: +v means x[v-1]=h,
-v means x[v-1]=1. Its logical clause negates each listed literal.
"""
from collections import defaultdict, Counter
from itertools import combinations, product
from functools import lru_cache
from pathlib import Path
import argparse
import json
import random
import time


def rectangle_sets(h, m):
    """Axis rectangles and tilted rectangles via perpendicular integer sides."""
    for r, s in combinations(range(1, h + 1), 2):
        for x, z in combinations(range(m), 2):
            yield frozenset(((x, r), (z, r), (x, s), (z, s)))
    for b in range(1, h):
        for d in range(1, h - b):
            for a in range(1, min(b * d, m - 2) + 1):
                if b * d % a:
                    continue
                c = b * d // a
                if a + c >= m:
                    continue
                for r in range(b + 1, h - d + 1):
                    for x in range(m - a - c):
                        yield frozenset(((x, r), (x + a, r - b),
                                         (x + c, r + d), (x + a + c, r - b + d)))


def cell(h, order, point):
    """Return (constant-black, literal), with zero literal for constants."""
    x, r = point
    j, rem = divmod(x, 4)
    if rem == 0:
        return r in order[j], 0
    if rem == 1:
        return r == 1, 0
    if rem == 3:
        return r == h, 0
    if r == 1:
        return False, -(j + 1)
    if r == h:
        return False, j + 1
    return False, 0


def required_black(h, order, points):
    needed = set()
    for p in points:
        fixed, literal = cell(h, order, p)
        if literal:
            if -literal in needed:
                return None
            needed.add(literal)
        elif not fixed:
            return None
    return tuple(sorted(needed, key=lambda x: (abs(x), x)))


def compile_constraints(h, order):
    m = 4 * len(order) - 3
    by_presentation = defaultdict(set)
    rectangles = 0
    candidates = 0
    for rect in rectangle_sets(h, m):
        rectangles += 1
        cells = {p: cell(h, order, p) for p in rect}
        if sum(fixed or bool(lit) for fixed, lit in cells.values()) < 2:
            continue
        variables = sorted({abs(lit) for fixed, lit in cells.values() if lit})
        for values in product((False, True), repeat=len(variables)):
            assignment = dict(zip(variables, values))
            visible = frozenset(p for p, (fixed, lit) in cells.items()
                                if not (assignment[abs(lit)] == (lit > 0) if lit else fixed))
            if len(visible) <= 2:
                by_presentation[visible].add(rect)
                candidates += 1
    constraints = {}
    for visible, rects in by_presentation.items():
        for first, second in combinations(sorted(rects, key=lambda r: tuple(sorted(r))), 2):
            condition = required_black(h, order, first ^ second)
            if condition is not None:
                constraints.setdefault(condition, (first, second))
    return constraints, {"rectangles": rectangles,
                         "candidate_presentations": candidates,
                         "distinct_presentations": len(by_presentation)}


def accepts(constraints, assignment):
    return not any(all(assignment[abs(v) - 1] == (v > 0) for v in clause)
                   for clause in constraints)


def solve_2sat(constraints, n):
    if any(len(c) > 2 for c in constraints):
        raise ValueError("A collision needs more than two middle variables")
    if () in constraints:
        return None
    graph = [[] for _ in range(2 * n)]
    reverse = [[] for _ in range(2 * n)]
    def vertex(lit):
        return 2 * (abs(lit) - 1) + int(lit > 0)
    for c in constraints:
        a, b = (c[0], c[0]) if len(c) == 1 else c
        for u, v in ((vertex(a), vertex(-b)), (vertex(b), vertex(-a))):
            graph[u].append(v)
            reverse[v].append(u)
    seen, finish = set(), []
    def visit(v):
        seen.add(v)
        for w in graph[v]:
            if w not in seen:
                visit(w)
        finish.append(v)
    for v in range(2 * n):
        if v not in seen:
            visit(v)
    component = [-1] * (2 * n)
    def label(v, c):
        component[v] = c
        for w in reverse[v]:
            if component[w] < 0:
                label(w, c)
    count = 0
    for v in reversed(finish):
        if component[v] < 0:
            label(v, count)
            count += 1
    if any(component[2*j] == component[2*j+1] for j in range(n)):
        return None
    answer = [component[2*j+1] > component[2*j] for j in range(n)]
    assert accepts(constraints, answer)
    return answer


def count_assignments(constraints, n):
    """Exact model count by unit propagation and memoized branching."""
    def normalized(cs):
        return tuple(sorted(set(tuple(sorted(c, key=lambda x: (abs(x), x))) for c in cs)))
    @lru_cache(None)
    def recurse(cs, remaining):
        if () in cs:
            return 0
        if not cs:
            return 1 << remaining
        units = [c[0] for c in cs if len(c) == 1]
        lit = units[0] if units else max((v for c in cs for v in c),
                                        key=lambda v: sum(abs(v) in map(abs, c) for c in cs))
        var = abs(lit)
        total = 0
        values = [lit < 0] if units else [False, True]
        for value in values:
            true_lit = var if value else -var
            # A forbidden cube containing a false literal cannot be violated.
            reduced = [tuple(v for v in c if v != true_lit)
                       for c in cs if -true_lit not in c]
            total += recurse(normalized(reduced), remaining - 1)
        return total
    return recurse(normalized(constraints), n)


def direct_diagonals(h, m):
    """Independent enumeration, by midpoint and squared diagonal length."""
    points = [(x, r) for x in range(m) for r in range(1, h + 1)]
    buckets = defaultdict(list)
    for a, b in combinations(points, 2):
        key = (a[0] + b[0], a[1] + b[1],
               (a[0] - b[0])**2 + (a[1] - b[1])**2)
        buckets[key].append((a, b))
    result = set()
    for pairs in buckets.values():
        for a, b in combinations(pairs, 2):
            rect = frozenset(a + b)
            if len(rect) == 4:
                result.add(rect)
    return result


def direct_valid(rects, h, order, assignment):
    seen = set()
    for rect in rects:
        visible = []
        for p in rect:
            fixed, lit = cell(h, order, p)
            black = assignment[abs(lit)-1] == (lit > 0) if lit else fixed
            if not black:
                visible.append(p)
        visible = frozenset(visible)
        if visible in seen:
            return False
        seen.add(visible)
    return True


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path)
    parser.add_argument("--height", type=int, default=7)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--verify", type=int, default=0)
    parser.add_argument("--exhaustive", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rng = random.Random(args.seed)
    if args.input:
        data = json.loads(args.input.read_text())
        h, order = data["h"], data["order"]
    else:
        h = args.height
        order = [(a, b) for a in range(1, h+1, 2) for b in range(2, h+1, 2)]
        rng.shuffle(order)
    start = time.monotonic()
    constraints, counts = compile_constraints(h, order)
    max_size = max(map(len, constraints), default=0)
    answer = solve_2sat(constraints, len(order)-1) if max_size <= 2 else None
    counts.update(height=h, width=4*len(order)-3, order=order,
                  constraints_by_size=dict(sorted(Counter(map(len, constraints)).items())),
                  two_sat=max_size <= 2, satisfiable=answer is not None,
                  assignment_rows=([h if v else 1 for v in answer] if answer is not None else None))
    counts["valid_middle_assignments"] = count_assignments(constraints, len(order)-1)
    if args.verify or args.exhaustive:
        rects = direct_diagonals(h, counts["width"])
        assert rects == set(rectangle_sets(h, counts["width"]))
        choices = (product((False, True), repeat=len(order)-1) if args.exhaustive else
                   ([bool(rng.getrandbits(1)) for _ in range(len(order)-1)] for _ in range(args.verify)))
        checked = 0
        for assignment in choices:
            assert accepts(constraints, assignment) == direct_valid(rects, h, order, assignment)
            checked += 1
        if answer is not None:
            assert direct_valid(rects, h, order, answer)
        counts["independent_assignments_checked"] = checked
        counts["independent_rectangles"] = len(rects)
    counts["seconds"] = round(time.monotonic()-start, 3)
    counts["constraints"] = [list(c) for c in sorted(constraints, key=lambda x: (len(x), x))]
    counts["certificates"] = [{"condition": c, "rectangles": [sorted(r) for r in constraints[c]]}
                              for c in sorted(constraints, key=lambda x: (len(x), x))]
    if max_size > 2:
        c = next(c for c in constraints if len(c) > 2)
        counts["long_clause_certificate"] = {"condition": c,
            "rectangles": [sorted(r) for r in constraints[c]]}
    if args.output:
        args.output.write_text(json.dumps(counts, indent=2) + "\n")
    print(json.dumps({k: v for k, v in counts.items() if k not in ("constraints", "certificates", "order")}, indent=2))


if __name__ == "__main__":
    main()
