"""Compare two SAT enumerations of five-row optima (point-variable encoding and column-type
encoding) as sorted lists of one-based point sets, recheck every model with
verify_narrow.collision, and describe the optima: Klein-group orbits (row reflection
j -> 6-j, column reversal i -> m+1-i), singleton rows, whether all singletons lie in a boundary
row, and the status of the published width-21 witness. Where a transfer count
(five_row_optima_dp.py) exists for the same family, its count is compared too.

Usage: python five_row_w21_compare.py WIDTH --pairs LABEL=FILE_A,FILE_B[,DP_FILE] ... [--out FILE]
Input files are outputs of five_row_enum_points.py / five_row_enum_types.py (one-based
points); DP_FILE an output of five_row_optima_dp.py. Output JSON is one-based.
"""
import argparse
import json
import os
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, ROOT)
import verify_narrow  # noqa: E402

DATA_DIR = os.path.join(HERE, '..', 'data')
ROWS = 5
PUBLISHED_DOUBLES = {1: (1, 2), 5: (1, 4), 9: (2, 3), 13: (3, 4), 17: (2, 5), 21: (4, 5)}


def published_witness():
    pts = set()
    for x in range(1, 22):
        if x in PUBLISHED_DOUBLES:
            pts.update((x, y) for y in PUBLISHED_DOUBLES[x])
        else:
            pts.add((x, 1))
    return tuple(sorted(pts))


def load(path):
    d = json.load(open(path))
    sets = sorted({tuple(sorted(tuple(p) for p in m['points'])) for m in d['models']})
    return d, sets


def images(s, cols):
    maps = [lambda x, y: (x, y), lambda x, y: (x, ROWS + 1 - y),
            lambda x, y: (cols + 1 - x, y), lambda x, y: (cols + 1 - x, ROWS + 1 - y)]
    return [tuple(sorted(f(x, y) for x, y in s)) for f in maps]


def describe(s, cols):
    prof = {}
    for x, y in s:
        prof.setdefault(x, []).append(y)
    singles = sorted({ys[0] for ys in prof.values() if len(ys) == 1})
    doubles = sorted((x, tuple(sorted(ys))) for x, ys in prof.items() if len(ys) == 2)
    return singles, doubles


def analyse(label, cols, file_a, file_b, dp_file, rects):
    da, sa = load(file_a)
    db, sb = load(file_b)
    union = sorted(set(sa) | set(sb))
    rechecked = {}
    for s in union:
        mask = sum(1 << ((y - 1) * cols + (x - 1)) for x, y in s)
        rechecked[s] = verify_narrow.collision(rects, mask) is None
    both_complete = bool(da.get('complete')) and bool(db.get('complete'))
    model_set = set(union)
    seen = set()
    orbit_sizes = Counter()
    orbits_inside = 0
    fixed = Counter()
    for s in union:
        if s in seen:
            continue
        imgs = images(s, cols)
        orbit = set(imgs)
        seen |= orbit
        orbit_sizes[len(orbit)] += 1
        if orbit <= model_set:
            orbits_inside += 1
        if imgs[1] == imgs[0]:
            fixed['row_reflection'] += 1
        if imgs[2] == imgs[0]:
            fixed['column_reversal'] += 1
        if imgs[3] == imgs[0]:
            fixed['half_turn'] += 1
    single_rows = Counter()
    boundary_one = boundary_any = 0
    for s in union:
        singles, doubles = describe(s, cols)
        single_rows[tuple(singles)] += 1
        if len(singles) == 1 and singles[0] in (1, ROWS):
            boundary_one += 1
        if all(r in (1, ROWS) for r in singles):
            boundary_any += 1
    wit = published_witness() if cols == 21 else None
    wimgs = images(wit, cols) if wit else None
    rec = {
        'label': label, 'file_a': os.path.basename(file_a), 'file_b': os.path.basename(file_b),
        'method_a': da.get('method'), 'solver_a': da.get('solver'),
        'method_b': db.get('method'), 'solver_b': db.get('solver'),
        'singleton_rows_allowed': da.get('singleton_rows_allowed'),
        'double_columns': da.get('double_columns'),
        'complete_a': da.get('complete'), 'status_a': da.get('status'),
        'complete_b': db.get('complete'), 'status_b': db.get('status'),
        'wall_seconds_a': da.get('wall_seconds'), 'wall_seconds_b': db.get('wall_seconds'),
        'clauses_a': da.get('clauses') or [p.get('clauses') for p in da.get('partitions', [])],
        'variables_a': da.get('variables') or [p.get('variables') for p in da.get('partitions', [])],
        'clauses_b': db.get('clauses'), 'variables_b': db.get('variables'),
        'count_a': len(sa), 'count_b': len(sb), 'count_union': len(union),
        'same_model_set': sa == sb,
        'exact_count_established_by_both_encodings': both_complete and sa == sb,
        'all_models_rechecked_valid': all(rechecked.values()),
        'models_failing_recheck': sum(1 for v in rechecked.values() if not v),
        'orbit_size_histogram': {str(k): v for k, v in sorted(orbit_sizes.items())},
        'orbits_entirely_inside_model_set': orbits_inside,
        'orbits_total': sum(orbit_sizes.values()),
        'fixed_point_counts': dict(fixed),
        'singleton_row_sets': {str(k): v for k, v in sorted(single_rows.items(), key=lambda kv: -kv[1])},
        'all_singletons_in_one_boundary_row': boundary_one,
        'all_singletons_in_boundary_rows': boundary_any,
        'published_witness_in_model_set': (wit in model_set) if wit else None,
        'published_witness_images_in_model_set': [i in model_set for i in wimgs] if wit else None,
    }
    if dp_file and os.path.exists(dp_file):
        dd = json.load(open(dp_file))
        r = dd['results'][0]
        rec['dp_count'] = r['count']
        rec['dp_per_partition'] = [(p['rows_a'], p['count']) for p in r['per_partition']]
        rec['dp_agrees_with_enumeration'] = both_complete and sa == sb and r['count'] == len(sa)
        if 'partitions' in da:
            rec['points_encoding_per_partition'] = [(p['two_rows'], p['models']) for p in da['partitions']]
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('width', type=int)
    ap.add_argument('--pairs', nargs='+', required=True)
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    cols = args.width
    rects = verify_narrow.rectangles(ROWS, cols)
    wit = published_witness() if cols == 21 else None
    out = {'grid': {'rows': ROWS, 'cols': cols},
           'coordinates': 'one-based (column, row), (1,1) top-left',
           'klein_group': 'row reflection j -> 6-j, column reversal i -> m+1-i, half turn',
           'families': []}
    if wit:
        imgs = images(wit, cols)
        out['published_witness'] = {
            'points': [list(p) for p in wit],
            'fixed_by_row_reflection': imgs[1] == imgs[0],
            'fixed_by_column_reversal': imgs[2] == imgs[0],
            'fixed_by_half_turn': imgs[3] == imgs[0],
            'orbit_size': len(set(imgs)),
            'half_turn_image': [list(p) for p in imgs[3]],
            'valid': verify_narrow.collision(rects, sum(1 << ((y - 1) * cols + (x - 1)) for x, y in wit)) is None,
            'half_turn_image_valid': verify_narrow.collision(rects, sum(1 << ((y - 1) * cols + (x - 1)) for x, y in imgs[3])) is None,
        }
    for spec in args.pairs:
        label, files = spec.split('=', 1)
        parts = files.split(',')
        fa, fb = parts[0], parts[1]
        dp = parts[2] if len(parts) > 2 else None
        rec = analyse(label, cols, os.path.join(DATA_DIR, fa), os.path.join(DATA_DIR, fb),
                      os.path.join(DATA_DIR, dp) if dp else None, rects)
        out['families'].append(rec)
        print(json.dumps({k: rec[k] for k in ('label', 'count_a', 'count_b', 'same_model_set',
                                               'exact_count_established_by_both_encodings',
                                               'all_models_rechecked_valid', 'orbit_size_histogram',
                                               'orbits_entirely_inside_model_set', 'fixed_point_counts',
                                               'all_singletons_in_one_boundary_row',
                                               'all_singletons_in_boundary_rows',
                                               'published_witness_in_model_set')}
                         | ({'dp_count': rec.get('dp_count'), 'dp_agrees': rec.get('dp_agrees_with_enumeration')}
                            if 'dp_count' in rec else {})))
    path = args.out or os.path.join(DATA_DIR, f'five_row_w{cols}_optima_report.json')
    with open(path, 'w') as f:
        json.dump(out, f, indent=1)
    print('->', path)


if __name__ == '__main__':
    main()
