"""Checks on the published width-21 witness of the five-row family: validity, its images under
the Klein group (row reflection, column reversal, half turn), and the one-sided paddings by
singleton columns in row 1 or row 5 on either side.

Rectangles come from the right-angle-triple enumerator and validity from the injectivity of the
visible-corner map (verify21_common_check); the rectangle count is also compared with
verify_narrow.rectangles, and every verdict with verify_narrow.collision, as a second route.
Output coordinates are one-based (column, row).
"""
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.abspath(os.path.join(HERE, '..', '..')))
import verify21_common_check as C  # noqa: E402
import verify_narrow  # noqa: E402

OUT = os.path.join(HERE, '..', 'data', 'verify21_witness_check.json')
ROWS = 5


def narrow_valid(points, rows, cols):
    black = verify_narrow.mask(points, cols)
    return verify_narrow.collision(verify_narrow.rectangles(rows, cols), black) is None


def describe(name, points, cols):
    t = time.time()
    rects = C.rectangles(ROWS, cols)
    coll = C.presentation_collision(rects, points)
    nv = narrow_valid(points, ROWS, cols)
    res = {'board': name, 'cols': cols, 'black_points': len(points),
           'rectangles_triples': len(rects),
           'rectangles_verify_narrow': len(verify_narrow.rectangles(ROWS, cols)),
           'valid_injective': coll is None, 'valid_verify_narrow': nv,
           'collision': None if coll is None else
           {'rect_1': C.one_based(coll[0]), 'rect_2': C.one_based(coll[1]),
            'visible': C.one_based(coll[0] - set(points))},
           'points': C.one_based(points), 'seconds': round(time.time() - t, 2)}
    assert (coll is None) == nv
    return res


def main():
    w = set(C.zero_based(C.WITNESS_21))
    cols = 21
    out = {'coordinates': 'one-based (column, row), (1,1) top-left', 'tests': []}
    out['tests'].append(describe('witness', w, cols))
    images = C.klein_images(w, ROWS, cols)
    names = ['identity', 'row_reflection', 'column_reversal', 'half_turn']
    out['klein'] = {'fixed_by': {n: (img == frozenset(w)) for n, img in zip(names, images)},
                    'orbit_size': len(set(images)),
                    'images': {n: C.one_based(img) for n, img in zip(names, images)},
                    'images_valid': {n: describe(n, set(img), cols)['valid_injective']
                                     for n, img in zip(names, images)}}
    half = images[3]
    out['klein']['half_turn_singleton_rows'] = sorted(
        {y + 1 for x, y in half if sum(1 for a, b in half if a == x) == 1})
    out['klein']['half_turn_double_columns'] = sorted(
        {x + 1 for x, y in half if sum(1 for a, b in half if a == x) == 2})
    # paddings
    for row_name, row in (('row-1', 0), ('row-5', 4)):
        for k in range(1, 6):
            right = set(w) | {(cols + i, row) for i in range(k)}
            out['tests'].append(describe(f'right padding, {k} {row_name} singleton columns',
                                         right, cols + k))
        left = {(x + 5, y) for x, y in w} | {(i, row) for i in range(5)}
        out['tests'].append(describe(f'left padding, 5 {row_name} singleton columns', left, cols + 5))
    with open(OUT, 'w') as f:
        json.dump(out, f, indent=1)
    for t in out['tests']:
        print(t['board'], t['cols'], t['rectangles_triples'], t['valid_injective'], t['collision'])
    print(json.dumps({k: v for k, v in out['klein'].items() if k != 'images'}, indent=1))


if __name__ == '__main__':
    main()
