"""Compare the model sets of two enumerations of the five-row optima at one width, recheck every
model, and describe the optima: Klein-group orbits (row reflection j -> 6-j and column
reversal i -> m+1-i, one-based), the orbit of the published width-21 witness, singleton rows,
and the double-column positions.

Usage: python five_row_compare_optima.py WIDTH FILE_A FILE_B [--out FILE]
Both input files are outputs of five_row_enum_structured.py or five_row_enum_unstructured.py
(one-based points). Output JSON is one-based.
"""
import argparse
import json
import os
from collections import Counter

from five_row_common import (DATA_DIR, collision_report, column_profile, klein_images, mask_of,
                             one_based, published_witness, verify_narrow, zero_based)

ROWS = 5


def load(path):
    d = json.load(open(path))
    sets = sorted(tuple(sorted(zero_based(m['points']))) for m in d['models'])
    return d, sets


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('width', type=int)
    ap.add_argument('file_a')
    ap.add_argument('file_b')
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    cols = args.width
    da, sa = load(args.file_a)
    db, sb = load(args.file_b)
    rects = verify_narrow.rectangles(ROWS, cols)

    # independent recheck here, not trusting the flags stored by the enumerators
    rechecked = {s: collision_report(rects, mask_of(s, cols), ROWS, cols) is None for s in set(sa) | set(sb)}
    union = sorted(set(sa) | set(sb))

    # orbits under the Klein group
    seen = set()
    orbits = []
    for s in union:
        if s in seen:
            continue
        imgs = klein_images(s, ROWS, cols)
        orbit = sorted(set(imgs))
        missing = [o for o in orbit if o not in rechecked]
        seen.update(orbit)
        orbits.append({'size': len(orbit), 'representative': one_based(s),
                       'fixed_by_row_reflection': imgs[1] == imgs[0],
                       'fixed_by_column_reversal': imgs[2] == imgs[0],
                       'fixed_by_half_turn': imgs[3] == imgs[0],
                       'images_missing_from_model_set': [one_based(o) for o in missing]})

    # structure of each optimum
    descr = []
    for s in union:
        prof = column_profile(s, ROWS, cols)
        singles = sorted({p[0] for p in prof if len(p) == 1})
        doubles = [(x, p) for x, p in enumerate(prof) if len(p) == 2]
        descr.append({'points': one_based(s),
                      'singleton_rows': [r + 1 for r in singles],
                      'all_singletons_in_one_boundary_row': len(singles) == 1 and singles[0] in (0, ROWS - 1),
                      'all_singletons_in_boundary_rows': all(r in (0, ROWS - 1) for r in singles),
                      'double_columns': [[x + 1, [r + 1 for r in p]] for x, p in doubles],
                      'column_sizes': Counter(len(p) for p in prof),
                      'valid': rechecked[s]})

    witness = tuple(sorted(published_witness())) if cols == 21 else None
    wit = None
    if witness is not None:
        imgs = klein_images(witness, ROWS, cols)
        wit = {'in_model_set': witness in rechecked,
               'orbit_size': len(set(imgs)),
               'fixed_by_row_reflection': imgs[1] == imgs[0],
               'fixed_by_column_reversal': imgs[2] == imgs[0],
               'fixed_by_half_turn': imgs[3] == imgs[0],
               'images_one_based': [one_based(o) for o in imgs],
               'all_images_in_model_set': all(o in rechecked for o in imgs)}

    out = {
        'grid': {'rows': ROWS, 'cols': cols},
        'file_a': os.path.basename(args.file_a), 'file_b': os.path.basename(args.file_b),
        'method_a': da.get('method'), 'solver_a': da.get('solver'), 'complete_a': da.get('complete'),
        'status_a': da.get('status'),
        'method_b': db.get('method'), 'solver_b': db.get('solver'), 'complete_b': db.get('complete'),
        'status_b': db.get('status'),
        'count_a': len(sa), 'count_b': len(sb), 'count_union': len(union),
        'same_model_set': sa == sb,
        'only_in_a': [one_based(s) for s in sorted(set(sa) - set(sb))],
        'only_in_b': [one_based(s) for s in sorted(set(sb) - set(sa))],
        'all_rechecked_valid': all(rechecked.values()),
        'orbit_count': len(orbits),
        'orbit_size_histogram': {str(k): v for k, v in sorted(Counter(o['size'] for o in orbits).items())},
        'orbits_with_images_missing_from_model_set': sum(1 for o in orbits if o['images_missing_from_model_set']),
        'orbits': orbits,
        'all_singletons_in_one_boundary_row_for_every_optimum': all(d['all_singletons_in_one_boundary_row'] for d in descr),
        'all_singletons_in_boundary_rows_for_every_optimum': all(d['all_singletons_in_boundary_rows'] for d in descr),
        'singleton_row_histogram': Counter(tuple(d['singleton_rows']) for d in descr),
        'published_witness': wit,
        'optima': descr,
        'coordinates': 'one-based (column, row), (1,1) top-left',
    }
    out['singleton_row_histogram'] = {str(k): v for k, v in out['singleton_row_histogram'].items()}
    for d in descr:
        d['column_sizes'] = {str(k): v for k, v in d['column_sizes'].items()}
    path = args.out or os.path.join(DATA_DIR, f'five_row_optima_w{cols}_summary.json')
    with open(path, 'w') as f:
        json.dump(out, f, indent=1)
    print(json.dumps({k: out[k] for k in ('count_a', 'count_b', 'count_union', 'same_model_set', 'all_rechecked_valid',
                                          'orbit_count', 'orbit_size_histogram',
                                          'orbits_with_images_missing_from_model_set',
                                          'all_singletons_in_one_boundary_row_for_every_optimum',
                                          'all_singletons_in_boundary_rows_for_every_optimum',
                                          'singleton_row_histogram', 'published_witness')}, indent=1))
    print('->', path)


if __name__ == '__main__':
    main()
