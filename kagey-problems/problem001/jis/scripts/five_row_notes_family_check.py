"""Check of the width-21 five-row board of the research notes and its padded versions.

The board (six doubles at columns 1, 5, 9, 13, 17, 21, top-row singletons in
every other column, 27 points on 5 x 21) is rebuilt here from its picture and
tested, together with the boards obtained by adding top-row singleton columns
on the right, on the left, and on both sides, at every width 21..120, with the
side-vector enumerator and the presentation test of five_row_geometry_check.
This checks the finite instances of the notes' family; the notes' proof for
every width is not recomputed here.

Output: jis/data/five_row_notes_family_check.json, one-based (column, row).
"""
import json
import os
import time

from five_row_geometry_check import rectangles_by_sides, presentation_collision, mask_from_one_based

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, '..', 'data')
ROWS = 5

PICTURE = ['########.###.###.###.',
           '#.......#.......#....',
           '........#...#........',
           '....#.......#.......#',
           '................#...#']


def base_points():
    return [(x + 1, y + 1) for y, line in enumerate(PICTURE) for x, ch in enumerate(line) if ch == '#']


def main():
    t0 = time.time()
    base = base_points()
    assert len(base) == 27
    out = {'coordinates': 'one-based (column,row)', 'base_width': 21, 'base_points': base,
           'base_picture': PICTURE, 'checks': []}
    for m in range(21, 121):
        k = m - 21
        rects = rectangles_by_sides(ROWS, m)
        variants = {
            'right': base + [(21 + i, 1) for i in range(1, k + 1)],
            'left': [(c + k, r) for c, r in base] + [(i, 1) for i in range(1, k + 1)],
            'both': [(c + k // 2, r) for c, r in base] + [(i, 1) for i in range(1, k // 2 + 1)]
                    + [(21 + k // 2 + i, 1) for i in range(1, k - k // 2 + 1)],
        }
        rec = {'width': m, 'rectangles': len(rects)}
        for name, pts in variants.items():
            assert len(pts) == m + 6
            rec[name] = presentation_collision(rects, mask_from_one_based(pts, m)) is None
        out['checks'].append(rec)
    out['all_valid'] = all(r['right'] and r['left'] and r['both'] for r in out['checks'])
    out['seconds'] = round(time.time() - t0, 1)
    with open(os.path.join(DATA, 'five_row_notes_family_check.json'), 'w') as f:
        json.dump(out, f, indent=1)
    print('notes width-21 board and padded versions valid at every width 21..120:', out['all_valid'],
          'seconds', out['seconds'])


if __name__ == '__main__':
    main()
