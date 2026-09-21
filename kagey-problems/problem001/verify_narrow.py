"""Independent checks for the three-row and four-row theorems.

Standard library only. Rectangles are generated from equal-length diagonals with
the same midpoint, independently of the tilted-template proof.
"""
from collections import Counter, defaultdict
from itertools import combinations, permutations, product


def rectangles(rows, cols):
    points = [(x, y) for y in range(rows) for x in range(cols)]
    diagonals = defaultdict(list)
    for i, j in combinations(range(len(points)), 2):
        x, y = points[i]
        xx, yy = points[j]
        diagonals[x + xx, y + yy, (x - xx) ** 2 + (y - yy) ** 2].append((i, j))
    result = set()
    for pairs in diagonals.values():
        for a, b in combinations(pairs, 2):
            corners = set(a + b)
            if len(corners) == 4:
                result.add(sum(1 << i for i in corners))
    return sorted(result)


def mask(points, cols):
    return sum(1 << (y * cols + x) for x, y in set(points))


def axis_rectangles(rows, cols):
    return [mask(((a, r), (a, s), (b, r), (b, s)), cols)
            for r, s in combinations(range(rows), 2)
            for a, b in combinations(range(cols), 2)]


def collision(rects, black):
    seen = {}
    for r in rects:
        visible = r & ~black
        if visible in seen:
            return seen[visible], r
        seen[visible] = r
    return None


def no_short_cycles(rows, cols, black):
    row_masks = [(black >> (y * cols)) & ((1 << cols) - 1) for y in range(rows)]
    common = {(a, b): row_masks[a] & row_masks[b]
              for a, b in combinations(range(rows), 2)}
    if any(v.bit_count() >= 2 for v in common.values()):
        return False
    for a, b, c in combinations(range(rows), 3):
        x, y, z = common[a, b], common[a, c], common[b, c]
        if x and y and z and len({x, y, z}) == 3:
            return False
    return True


def tilted_templates(rows, cols):
    found = set()
    for y in range(rows - 2):
        for x in range(cols - 2):
            found.add(mask(((x, y + 1), (x + 1, y),
                            (x + 2, y + 1), (x + 1, y + 2)), cols))
    if rows == 4:
        for x in range(cols - 3):
            for a, b, c, d in ((1, 1, 2, 2), (2, 1, 1, 2),
                               (1, 2, 2, 1), (2, 2, 1, 1)):
                found.add(mask(((x, d), (x + a, 3), (x + c, 0), (x + 3, b)), cols))
    return found


def four_row_construction(cols):
    return mask({(x, 0) for x in range(1, cols - 1)} |
                {(cols - 2, 1), (cols - 1, 1), (0, 2), (1, 2),
                 (0, 3), (cols - 1, 3)}, cols)


def four_row_upper_candidates(cols):
    """All possible equality cases of the m+4 upper bound, for m=4,5."""
    for partner in (1, 2, 3):
        left = (0, partner)
        right = tuple(r for r in range(4) if r not in left)
        edges = list(product(left, right))
        for double_cols in combinations(range(cols), 4):
            single_cols = sorted(set(range(cols)) - set(double_cols))
            for edge_order in permutations(edges):
                fixed = {(x, y) for x, edge in zip(double_cols, edge_order) for y in edge}
                for single_rows in product(range(4), repeat=len(single_cols)):
                    yield mask(fixed | set(zip(single_cols, single_rows)), cols)


def main():
    tested = 0
    for rows, cols in ((2, 3), (3, 3), (3, 4), (4, 3), (4, 4)):
        axis = axis_rectangles(rows, cols)
        for black in range(1 << (rows * cols)):
            assert (collision(axis, black) is None) == no_short_cycles(rows, cols, black)
            tested += 1
    print(f'PASS: axis characterization on all {tested} blackouts of five small grids.')

    widths = list(range(3, 41)) + [64, 100, 128]
    for rows in (3, 4):
        for cols in widths:
            all_rects = rectangles(rows, cols)
            axis = set(axis_rectangles(rows, cols))
            assert set(all_rects) - axis == tilted_templates(rows, cols)
            if rows == 3:
                black = mask({(x, 0) for x in range(cols)} | {(0, 1), (0, 2)}, cols)
                assert black.bit_count() == cols + 2
            elif cols >= 6:
                black = four_row_construction(cols)
                assert black.bit_count() == cols + 4
            else:
                continue
            assert collision(all_rects, black) is None, (rows, cols)
    print('PASS: complete tilted-template lists and constructions through width 128 (sampled widths).')

    for cols, expected in ((4, 72), (5, 1440)):
        rects = rectangles(4, cols)
        axis = set(axis_rectangles(4, cols))
        candidates = set(four_row_upper_candidates(cols))
        assert len(candidates) == expected
        types = Counter()
        for black in candidates:
            assert black.bit_count() == cols + 4
            assert no_short_cycles(4, cols, black)
            pair = collision(rects, black)
            assert pair is not None, (cols, black)
            types[sum(r in axis for r in pair)] += 1
        cross = mask({(x, 0) for x in range(cols)} | {(0, y) for y in range(4)}, cols)
        assert cross.bit_count() == cols + 3
        assert collision(rects, cross) is None
        print(f'PASS: all {expected} upper-bound candidates fail on 4x{cols}; '
              f'valid blackout of size {cols + 3}; collision axis counts {dict(types)}.')
    print('All narrow-grid checks passed. The general-width claims use the accompanying proofs.')


if __name__ == '__main__':
    main()
