"""Independent pair geometry for the linear boundary star at spacing p>h."""
from itertools import combinations
from pathlib import Path
import json
import time

from verify_low_two_sea_one_label import pair_rectangles

HERE = Path(__file__).resolve().parent


def check(h):
    spacing = 4 * ((h + 4) // 4)
    assert spacing > h and spacing % 4 == 0
    span = 1 + (h - 1) ** 2 // 4
    offset = 2 * span
    width = spacing * (h // 2 - 1) + 1 + 2 * offset
    cols = [{0} for _ in range(width)]
    extras = [(offset + spacing * i, 2 * i + 1) for i in range(h // 2)]
    for x, r in extras:
        cols[x].add(r)
    base = [(x, 0) for x in range(width)]
    rectangles = pair_rectangles(h, width,
        ((A, B) for A in extras for B in base))
    rectangles.update(pair_rectangles(h, width, combinations(extras, 2)))
    black = {r * width + x for x, rows in enumerate(cols) for r in rows}
    presentations = {}
    for R in rectangles:
        white = tuple(p for p in R if p not in black)
        assert white and white not in presentations, (h, R, white)
        presentations[white] = R
        if len(white) == 1:
            x, r = white[0] % width, white[0] // width
            assert not any((r - s) % 2 for s in cols[x]), ('singleton', h, R)
        else:
            assert len(white) == 2
            x, r = white[0] % width, white[0] // width
            z, s = white[1] % width, white[1] // width
            if x == z:
                assert not (r - s) % 2, ('vertical', h, R)
            elif r == s:
                assert not cols[x] & cols[z], ('horizontal', h, R)
            else:
                assert not (s in cols[x] and r in cols[z]), ('oblique', h, R)
    return {'height': h, 'spacing': spacing, 'core_width': spacing * (h // 2 - 1) + 1,
            'checked_width': width, 'weak_tilted_rectangles': len(rectangles),
            'status': 'PASS'}


def main():
    begin = time.monotonic()
    records = []
    for h in range(4, 31):
        records.append(check(h))
        print(json.dumps(records[-1]), flush=True)
        (HERE / 'wide_linear_star_check.json').write_text(json.dumps(
            {'results': records, 'seconds': time.monotonic() - begin}, indent=2) + '\n')


if __name__ == '__main__':
    main()
