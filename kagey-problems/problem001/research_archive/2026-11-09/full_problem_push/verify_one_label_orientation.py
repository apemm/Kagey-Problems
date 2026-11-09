"""Independent pair geometry for the one-label orientation lemma.

All noncentral double slots are holes. Singleton/vertical axis rivals use
the final parity graph, while horizontal/oblique rivals use actual black
points. Thus these checks concern supports using at most one double label.
"""
from pathlib import Path
import json
import time

from verify_parity_board_pair_geometry import tilted_pairs

HERE = Path(__file__).resolve().parent


def check(h, odd, even):
    span = 1 + ((h - 1) // 2) ** 2
    center = 8 * ((2 * span + 7) // 8)
    width = 2 * center + 1
    cols = [set() if x % 8 == 0 else {h - 1 if x % 8 == 4 else 0}
            for x in range(width)]
    if odd is not None:
        cols[center] = {odd - 1, even - 1}
    points = [(x, r) for x, rows in enumerate(cols) for r in rows]
    black = {r * width + x for x, r in points}
    presentations = {}
    rectangles = tilted_pairs(h, width, points)
    for rectangle in rectangles:
        white = tuple(p for p in rectangle if p not in black)
        assert white and white not in presentations, (h, odd, even, rectangle, white)
        presentations[white] = rectangle
        if len(white) == 1:
            x, r = white[0] % width, white[0] // width
            assert x % 8 and not any((r - s) % 2 for s in cols[x])
        else:
            assert len(white) == 2
            x, r = white[0] % width, white[0] // width
            z, s = white[1] % width, white[1] // width
            if x == z:
                assert not (r - s) % 2
            elif r == s:
                assert not cols[x] & cols[z]
            else:
                assert not (s in cols[x] and r in cols[z])
    return len(rectangles)


def main():
    begin = time.monotonic()
    counts = []
    for h in (7, 11, 15, 19):
        cases = 1
        rectangles = check(h, None, None)
        for odd in range(1, h + 1, 4):
            for even in range(2, h + 1, 2):
                rectangles += check(h, odd, even)
                cases += 1
        counts.append({'height': h, 'cases': cases,
                       'weak_tilted_rectangles': rectangles})
        print(json.dumps(counts[-1]), flush=True)
    result = {'status': 'PASS', 'heights': counts,
              'seconds': time.monotonic() - begin}
    (HERE / 'one_label_orientation_check.json').write_text(
        json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
