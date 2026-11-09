"""Exact periodic pair geometry for (g,1,2,1), using period-four translation."""
from pathlib import Path
import json
from verify_low_two_sea_one_label import pair_rectangles

HERE = Path(__file__).resolve().parent


def check(h, g):
    span = 1 + (h - 1) ** 2 // 4
    center = 4 * ((2 * span + 3) // 4)
    width = 2 * center + 5
    row = lambda x: (g - 1, 0, 1, 0)[x % 4]
    pairs = (((center + a, row(a)), (center + a + d, row(a + d)))
             for a in range(4) for d in range(1, span + 1))
    rectangles = pair_rectangles(h, width, pairs)
    seen = {}
    for R in rectangles:
        points = [(p % width, p // width) for p in R]
        white = tuple(sorted((x, y) for x, y in points if row(x) != y))
        if not white:
            return {'h': h, 'g': g, 'bad': 'hidden', 'R': points}
        shift = 4 * (min(x for x, y in white) // 4)
        key = tuple((x - shift, y) for x, y in white)
        canon = tuple(sorted((x - shift, y) for x, y in points))
        if key in seen and seen[key] != canon:
            return {'h': h, 'g': g, 'bad': 'duplicate', 'R': canon,
                    'other': seen[key], 'white': key}
        seen[key] = canon
        if len(white) == 1:
            x, y = white[0]
            if (row(x) - y) % 2:
                return {'h': h, 'g': g, 'bad': 'singleton', 'R': canon}
        else:
            assert len(white) == 2
            (x, r), (z, s) = white
            if (x == z and (r - s) % 2 or r == s and row(x) == row(z)
                or x != z and r != s and row(x) == s and row(z) == r):
                return {'h': h, 'g': g, 'bad': 'pair_axis', 'R': canon}
    return {'h': h, 'g': g, 'status': 'PASS', 'rectangles': len(rectangles)}


def main():
    constant = [check(h, 4) for h in range(4, 101)]
    assert all(r.get('status') == 'PASS' for r in constant)
    top = [check(h, h if h % 2 == 0 else h - 1) for h in range(4, 31)]
    result = {'constant_four': constant, 'top_even': top}
    (HERE / 'periodic_low_four_sea_check.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'constant_four_passed': len(constant),
                      'top_even_passed': [r['h'] for r in top if r.get('status') == 'PASS']}))


if __name__ == '__main__':
    main()
