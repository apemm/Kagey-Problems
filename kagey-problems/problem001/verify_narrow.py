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


def short_cycle_free_sets(rows, cols):
    """All blackouts whose incidence graph has no 4- or 6-cycle, grouped by size."""
    cells = [(x, y) for y in range(rows) for x in range(cols)]
    found = defaultdict(list)

    def extend(i, black):
        if i == len(cells):
            found[black.bit_count()].append(black)
            return
        extend(i + 1, black)
        bigger = black | mask([cells[i]], cols)
        if no_short_cycles(rows, cols, bigger):
            extend(i + 1, bigger)

    extend(0, 0)
    return found


def square_images(black, n):
    """The 8 images of a blackout on an n x n grid under the symmetries of the square."""
    points = [(x, y) for y in range(n) for x in range(n) if black >> (y * n + x) & 1]
    maps = [lambda x, y: (x, y), lambda x, y: (n - 1 - y, x),
            lambda x, y: (n - 1 - x, n - 1 - y), lambda x, y: (y, n - 1 - x),
            lambda x, y: (n - 1 - x, y), lambda x, y: (x, n - 1 - y),
            lambda x, y: (y, x), lambda x, y: (n - 1 - y, n - 1 - x)]
    return [mask([f(x, y) for x, y in points], n) for f in maps]


def check_five_by_five():
    """Theorem on the 5 x 5 grid: value 10, 8 optima in one orbit, 8-cycle graphs."""
    rects = rectangles(5, 5)
    assert len(rects) == 130
    found = short_cycle_free_sets(5, 5)
    assert max(found) == 10                  # the lemma on 10 vertices, by brute force
    candidates = found[10]
    assert len(candidates) == 44640
    optima = [b for b in candidates if collision(rects, b) is None]
    assert len(optima) == 8
    # the representative of the paper, rows top to bottom, '#' = blacked out
    picture = ['..###', '..#..', '.##..', '##...', '#...#']
    rep = mask([(x, y) for y in range(5) for x in range(5) if picture[y][x] == '#'], 5)
    images = square_images(rep, 5)
    assert len(set(images)) == 8 and set(images) == set(optima)

    def degrees(b):
        rows = [((b >> (5 * y)) & 31).bit_count() for y in range(5)]
        cols = [sum(b >> (5 * y + x) & 1 for y in range(5)) for x in range(5)]
        return rows, cols

    ten_cycles = [b for b in candidates if degrees(b) == ([2] * 5, [2] * 5)]
    assert not any(collision(rects, b) is None for b in ten_cycles)
    for b in optima:                          # an 8-cycle plus 2 pendant edges
        rows, cols = degrees(b)
        assert sorted(rows + cols) == [1, 1] + [2] * 6 + [3, 3]
    return len(candidates), len(ten_cycles)


def check_game_witnesses():
    """Second check of the staircase-plus-one blackouts stored in game/game.js (n+m points)."""
    import os
    import re
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'game', 'game.js')
    if not os.path.exists(path):
        return None
    src = open(path).read()
    start = src.index('var WITNESS = {')
    block = src[start:src.index('};', start)]
    checked = []
    for key, body in re.findall(r"'(\d+x\d+)': \[([^\]]*)\]", block):
        rows, cols = map(int, key.split('x'))
        picture = re.findall(r"'([.#]+)'", body)
        assert len(picture) == rows and all(len(r) == cols for r in picture)
        black = mask([(x, y) for y in range(rows) for x in range(cols) if picture[y][x] == '#'], cols)
        assert black.bit_count() == rows + cols, key
        assert collision(rectangles(rows, cols), black) is None, key
        checked.append(key)
    return checked


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
    total, ten = check_five_by_five()
    print(f'PASS: 5x5 has no valid blackout of size 11; of the {total} 10-point sets with no '
          f'short cycle, exactly 8 are valid, one D4 orbit of the paper\'s representative, each an '
          f'8-cycle with 2 pendant edges; none of the {ten} 10-cycles is valid.')
    for rows in range(2, 11):
        for cols in range(rows, 11):
            cross = mask({(x, 0) for x in range(cols)} | {(0, y) for y in range(rows)}, cols)
            assert collision(rectangles(rows, cols), cross) is None, (rows, cols)
    print('PASS: row 1 plus column 1 (n+m-1 points) is valid on every grid up to 10x10.')
    checked = check_game_witnesses()
    if checked:
        print(f'PASS: the {len(checked)} blackouts of n+m points stored in game/game.js '
              f'({checked[0]} to {checked[-1]}) are valid.')
    print('All narrow-grid checks passed. The general-width claims use the accompanying proofs.')


if __name__ == '__main__':
    main()
