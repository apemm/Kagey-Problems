"""Independent construction audit; no imports from the existing checkers.

Certifies necessary conditions from geometric witnesses, then directly checks
all 384 survivors by presentation equality. Rectangle enumeration uses equal
diagonals, not the original perpendicular-side compiler.
"""
from collections import defaultdict
from itertools import combinations, product
from pathlib import Path
from math import prod
import json
import time


def is_rectangle(points):
    p = tuple(points)
    if len(set(p)) != 4:
        return False
    for j in (1, 2, 3):
        rest = [i for i in (1, 2, 3) if i != j]
        a, b, c, d = p[0], p[j], p[rest[0]], p[rest[1]]
        if (a[0] + b[0], a[1] + b[1]) != (c[0] + d[0], c[1] + d[1]):
            continue
        if sum((a[t] - b[t]) ** 2 for t in (0, 1)) == sum((c[t] - d[t]) ** 2 for t in (0, 1)):
            return True
    return False


def fixed_or_literal(h, order, x, y):
    block, residue = divmod(x, 4)
    if residue == 0:
        return y in order[block], 0
    if residue == 1:
        return y == 1, 0
    if residue == 3:
        return y == h, 0
    if y == 1:
        return False, -(block + 1)
    if y == h:
        return False, block + 1
    return False, 0


def certified_necessary_conditions(data):
    h, order = data["height"], data["order"]
    conditions = []
    for certificate in data["certificates"]:
        first, second = [set(map(tuple, points)) for points in certificate["rectangles"]]
        assert first != second and is_rectangle(first) and is_rectangle(second)
        required = set()
        for x, y in first ^ second:
            fixed, literal = fixed_or_literal(h, order, x, y)
            assert fixed or literal
            if literal:
                assert -literal not in required
                required.add(literal)
        assert required == set(certificate["condition"])
        conditions.append(tuple(required))
    assert {frozenset(c) for c in conditions} == {frozenset(c) for c in data["constraints"]}
    return conditions


def enumerate_survivors(conditions, n):
    adjacency = [set() for _ in range(n)]
    for condition in conditions:
        variables = [abs(lit) - 1 for lit in condition]
        for a in variables:
            adjacency[a].update(variables)
    unseen = set(range(n))
    choices = []
    sizes = []
    while unseen:
        stack = [min(unseen)]
        component = set()
        while stack:
            v = stack.pop()
            if v in component:
                continue
            component.add(v)
            stack.extend(adjacency[v] - component)
        unseen -= component
        variables = sorted(component)
        local = [c for c in conditions if abs(c[0]) - 1 in component]
        allowed = []
        for bits in product((False, True), repeat=len(variables)):
            values = dict(zip(variables, bits))
            if any(all(values[abs(lit) - 1] == (lit > 0) for lit in c) for c in local):
                continue
            allowed.append(sum(1 << j for j, bit in values.items() if bit))
        choices.append(allowed)
        sizes.append({"variables": [j + 1 for j in variables], "count": len(allowed)})
    survivors = [sum(parts) for parts in product(*choices)]
    assert len(survivors) == prod(c["count"] for c in sizes)
    return survivors, sizes


def equal_diagonal_rectangles(h, width):
    points = [(x, y) for x in range(width) for y in range(1, h + 1)]
    groups = defaultdict(list)
    for i, (x, y) in enumerate(points):
        for j in range(i + 1, len(points)):
            z, t = points[j]
            groups[(x + z, y + t, (x - z) ** 2 + (y - t) ** 2)].append((i, j))
    for diagonals in groups.values():
        for first, second in combinations(diagonals, 2):
            assert len(set(first + second)) == 4
            yield first + second


def direct_middle_audit(data, survivors):
    h, order, width = data["height"], data["order"], data["width"]
    fixed_black = variable_cells = 0
    choices = []
    for x in range(width):
        for y in range(1, h + 1):
            fixed, literal = fixed_or_literal(h, order, x, y)
            bit = 1 << (x * h + y - 1)
            if fixed:
                fixed_black |= bit
            if literal:
                variable_cells |= bit
    for j in range(len(order) - 1):
        x = 4 * j + 2
        choices.append((1 << (x * h), 1 << (x * h + h - 1)))
    possible_black = fixed_black | variable_cells
    all_rectangles = 0
    candidates = []
    for corners in equal_diagonal_rectangles(h, width):
        all_rectangles += 1
        mask = sum(1 << i for i in corners)
        if (mask & ~possible_black).bit_count() <= 2:
            candidates.append(mask)
    failures = []
    for assignment in survivors:
        black = fixed_black
        for j, pair in enumerate(choices):
            black |= pair[(assignment >> j) & 1]
        white_mask = ~black
        presentations = set()
        for rectangle in candidates:
            visible = rectangle & white_mask
            if visible.bit_count() > 2:
                continue
            if visible in presentations:
                failures.append(assignment)
                break
            presentations.add(visible)
    return {"rectangles": all_rectangles,
            "possibly_weak_rectangles": len(candidates),
            "assignments_checked_directly": len(survivors),
            "direct_failures": failures}


def audit_q_t_examples():
    examples = {
        "T": (((0, 3), (4, 11), (2, 2), (6, 10)),
              ((0, 4), (8, 8), (2, 2), (6, 10)),
              ((0, 3), (0, 4), (4, 2), (4, 11), (8, 1), (8, 8))),
        "Q": (((0, 9), (4, 13), (8, 1), (12, 5)),
              ((8, 5), (12, 1), (8, 1), (12, 5)),
              ((0, 2), (0, 9), (4, 4), (4, 13), (8, 5), (8, 6), (12, 1), (12, 8))),
    }
    result = {}
    for name, (first, second, black) in examples.items():
        assert is_rectangle(first) and is_rectangle(second)
        black = set(black)
        assert set(first) - black == set(second) - black
        angles = 0
        for vertex in black:
            for a, b in combinations(black - {vertex}, 2):
                angles += sum((a[j] - vertex[j]) * (b[j] - vertex[j]) for j in (0, 1)) == 0
        assert angles == 0
        result[name] = {"rectangles_valid": True, "same_presentation": True,
                        "black_right_angles": angles}
    return result


def audit_p_boundary_correction():
    tilted = {(0, 2), (4, 5), (2, 1), (2, 6)}
    axis = {(2, 1), (2, 6), (8, 1), (8, 6)}
    assert is_rectangle(tilted) and is_rectangle(axis)
    fixed_black = {(0, 1), (0, 2), (4, 4), (4, 5), (8, 1), (8, 6)}
    presentations = {}
    for middle_row in range(1, 8):
        black = fixed_black | {(2, middle_row)}
        first = tilted - black
        second = axis - black
        assert first == second
        presentations[str(middle_row)] = sorted(first)
    return {"height": 7, "three_double_patch_width": 9,
            "tilted": sorted(tilted), "axis": sorted(axis),
            "presentations_for_every_middle_row": presentations}


def main():
    start = time.monotonic()
    source = Path(__file__).resolve().parent.parent / "middle_count_h11.json"
    data = json.loads(source.read_text())
    conditions = certified_necessary_conditions(data)
    survivors, components = enumerate_survivors(conditions, len(data["order"]) - 1)
    assert len(survivors) == 384
    direct = direct_middle_audit(data, survivors)
    assert direct["rectangles"] == 435307 and not direct["direct_failures"]
    output = {"necessary_conditions_certified": len(conditions),
              "component_counts": components, "middle_count": 384,
              "direct_presentation_check": direct,
              "Q_T": audit_q_t_examples(),
              "P_boundary_correction": audit_p_boundary_correction(),
              "seconds": round(time.monotonic() - start, 3)}
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
