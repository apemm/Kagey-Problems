"""Recheck of stored width-21 optima: every point set in the given JSON files (lists of
one-based (column, row) points under the key "models", each entry a dict with "points") is
tested with the injectivity of the visible-corner map over the rectangles of the
right-angle-triple enumerator, its equality structure is read off, and the statistics on the
singleton rows and on fixed points under the Klein group are recomputed from scratch.

Usage: python verify21_models_check.py TAG FILE [FILE ...]
"""
import json
import os
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import verify21_common_check as C  # noqa: E402

DATA = os.path.join(HERE, '..', 'data')


def main():
    tag = sys.argv[1]
    files = sys.argv[2:]
    rows, cols = 5, 21
    rects = C.rectangles(rows, cols)
    all_sets = set()
    per_file = []
    invalid = 0
    for fn in files:
        with open(fn) as f:
            d = json.load(f)
        sets = []
        for entry in d['models']:
            pts = frozenset(C.zero_based(entry['points']))
            assert len(pts) == 27
            if not C.is_valid(rects, pts):
                invalid += 1
            sets.append(pts)
        per_file.append({'file': os.path.basename(fn), 'models': len(sets),
                         'distinct': len(set(sets))})
        all_sets.update(sets)
    srow_hist = Counter()
    boundary_only = 0
    one_boundary_row = 0
    all_five = 0
    fixed = Counter()
    orbit_sizes = Counter()
    no_structure = 0
    for pts in all_sets:
        shape = C.equality_shape(pts, rows, cols)
        if shape is None:
            no_structure += 1
            continue
        singles = tuple(r + 1 for r in shape[3])
        srow_hist[singles] += 1
        if set(singles) <= {1, 5}:
            boundary_only += 1
        if len(singles) == 1 and singles[0] in (1, 5):
            one_boundary_row += 1
        if len(singles) == 5:
            all_five += 1
        imgs = C.klein_images(pts, rows, cols)
        for name, img in zip(('row_reflection', 'column_reversal', 'half_turn'), imgs[1:]):
            if img == pts:
                fixed[name] += 1
        orbit_sizes[len(set(imgs))] += 1
    out = {'files': per_file, 'distinct_optima': len(all_sets), 'invalid': invalid,
           'without_equality_structure': no_structure,
           'singleton_rows_all_five': all_five,
           'singletons_only_in_boundary_rows': boundary_only,
           'singletons_in_one_boundary_row': one_boundary_row,
           'fixed_points': dict(fixed), 'orbit_sizes': {str(k): v for k, v in orbit_sizes.items()},
           'singleton_row_sets': {','.join(map(str, k)): v for k, v in srow_hist.most_common()}}
    with open(os.path.join(DATA, f'verify21_models_{tag}.json'), 'w') as f:
        json.dump(out, f, indent=1)
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()
