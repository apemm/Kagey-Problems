"""Recheck of every five-row witness and model list with the side-vector enumerator.

Reads the five-row result files in jis/data (one-based (column, row) point
lists), rebuilds each board as a bit mask, and tests it with
five_row_geometry_check (rectangles from a corner and two perpendicular side
vectors; presentation map injective).  Also rebuilds, from their definitions
rather than from the files, the staircase-plus-one board at every width 8..20,
the width-8 collar family at every width 8..120, and the boards quoted in the
five-row report, and checks the symmetry orbit of the four width-8 optima.

Output: jis/data/five_row_witness_check.json, one-based coordinates.
"""
import json
import os
import time
from collections import Counter
from itertools import combinations

from five_row_geometry_check import (rectangles_by_sides, presentation_collision,
                                     mask_from_one_based)

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, '..', 'data')
ROWS = 5

RECTS = {}


def rects(cols):
    if cols not in RECTS:
        RECTS[cols] = rectangles_by_sides(ROWS, cols)
    return RECTS[cols]


def check_board(points, cols):
    black = mask_from_one_based(points, cols)
    assert black.bit_count() == len(set(map(tuple, points)))
    return presentation_collision(rects(cols), black) is None, black


def load(name):
    with open(os.path.join(DATA, name)) as f:
        return json.load(f)


def column_structure(points):
    cols = Counter(c for c, r in points)
    doubles = sorted(tuple(sorted(r for c2, r in points if c2 == c)) for c, k in cols.items() if k == 2)
    return {'column_sizes': sorted(cols.values()), 'doubles': doubles}


def is_k23(doubles, rows=5):
    """Six row pairs forming a complete bipartite graph between a 2-set and a 3-set of rows."""
    if len(doubles) != 6 or len(set(doubles)) != 6:
        return False
    for two in combinations(range(1, rows + 1), 2):
        three = [r for r in range(1, rows + 1) if r not in two]
        edges = sorted(tuple(sorted((a, b))) for a in two for b in three)
        if edges == sorted(doubles):
            return True
    return False


def main():
    t0 = time.time()
    out = {'coordinates': 'one-based (column,row)',
           'enumerator': 'corner plus two perpendicular side vectors',
           'presentation_test': 'injectivity of visible corner sets over all rectangles'}

    # 1. Witnesses from the three SAT methods.
    witnesses = []
    for name, key in [('five_row_structured_cadical153.json', 'A'),
                      ('five_row_column_glucose4.json', 'B'),
                      ('five_row_unstructured_cadical153.json', 'U'),
                      ('five_row_unstructured_cadical153_w11_12.json', 'U')]:
        for inst in load(name)['instances']:
            pts = inst.get('witness_one_based')
            if not pts:
                continue
            m = inst['width']
            ok, _ = check_board(pts, m)
            rec = {'source': key, 'file': name, 'width': m, 'points': len(pts), 'excess': len(pts) - m,
                   'valid': ok, 'partition': inst.get('partition_rows_one_based'), 'bound': inst.get('bound')}
            st = column_structure(pts)
            rec['doubles_form_K23'] = is_k23(st['doubles']) if len(pts) == m + 6 else None
            rec['max_column_size'] = max(st['column_sizes'])
            witnesses.append(rec)
    out['sat_witnesses'] = witnesses
    out['sat_witnesses_all_valid'] = all(w['valid'] for w in witnesses)
    out['m_plus_6_witness_widths'] = sorted({w['width'] for w in witnesses if w['valid'] and w['excess'] == 6})
    out['m_plus_6_witnesses_by_source'] = {
        k: sorted({w['width'] for w in witnesses if w['valid'] and w['excess'] == 6 and w['source'] == k})
        for k in 'ABU'}
    out['m_plus_5_witness_widths'] = sorted({w['width'] for w in witnesses if w['valid'] and w['excess'] == 5})
    out['m_plus_6_all_K23'] = all(w['doubles_form_K23'] for w in witnesses if w['valid'] and w['excess'] == 6)

    # 2. Boards quoted in the report, rebuilt from the text.
    quoted = {
        'width8_representative': (8, [(1, 1), (1, 2), (2, 2), (2, 3), (3, 3), (3, 4), (4, 5), (5, 5), (6, 2),
                                      (6, 5), (7, 4), (7, 5), (8, 1), (8, 4)]),
        'width9_A_witness': (9, [(1, 4), (1, 5), (2, 1), (2, 2), (3, 2), (3, 4), (4, 4), (5, 4), (6, 4), (7, 3),
                                 (7, 4), (8, 1), (8, 3), (9, 1), (9, 5)]),
        'family_base_width8': (8, [(1, 1), (1, 4), (2, 4), (2, 5), (3, 2), (3, 5), (4, 5), (5, 5), (6, 3), (6, 4),
                                   (7, 2), (7, 3), (8, 1), (8, 2)]),
    }
    out['quoted_boards'] = {}
    for k, (m, pts) in quoted.items():
        ok, _ = check_board(pts, m)
        out['quoted_boards'][k] = {'width': m, 'points': len(pts), 'valid': ok}

    # 3. Staircase plus one: from the files, and rebuilt from the shape at every width 8..20.
    stair = []
    for inst in load('five_row_staircase_witnesses.json')['instances']:
        m = inst['width']
        pts = inst['witness_one_based']
        ok, _ = check_board(pts, m)
        stair.append({'width': m, 'points': len(pts), 'valid': ok, 'from': 'file'})
    for m in range(8, 21):
        # column 1 rows 1..3, column 2 rows 3..4, column 3 rows 4..5, row 5 from column 4 to m, corner (m,1)
        pts = [(1, 1), (1, 2), (1, 3), (2, 3), (2, 4), (3, 4), (3, 5)] + [(c, 5) for c in range(4, m + 1)] + [(m, 1)]
        ok, _ = check_board(pts, m)
        stair.append({'width': m, 'points': len(pts), 'valid': ok, 'from': 'rebuilt shape',
                      'excess': len(pts) - m})
    out['staircase_plus_one'] = stair
    out['staircase_all_valid'] = all(s['valid'] for s in stair)

    # 4. The four width-8 optima and their orbit under row reflection and column reversal.
    cand = load('five_row_width8_candidates.json')
    optima = [[tuple(p) for p in b] for b in cand['optima_one_based']]
    masks = []
    for b in optima:
        ok, bm = check_board(b, 8)
        masks.append(bm)
        assert ok and len(b) == 14
    rep = quoted['width8_representative'][1]

    def refl(pts):
        return sorted((c, 6 - r) for c, r in pts)

    def rev(pts, m=8):
        return sorted((m + 1 - c, r) for c, r in pts)

    orbit = {tuple(sorted(rep)), tuple(refl(rep)), tuple(rev(rep)), tuple(rev(refl(rep)))}
    out['width8_optima'] = {'count_in_file': len(optima), 'all_valid': True,
                            'distinct': len(set(masks)) == len(masks),
                            'orbit_of_representative_size': len(orbit),
                            'file_optima_equal_orbit': {tuple(sorted(b)) for b in optima} == orbit}

    # 5. The collar family at every width 8..120, rebuilt from its definition.
    base = quoted['family_base_width8'][1]
    fam = []
    for m in range(8, 121):
        pts = base + [(8 + i, 1) for i in range(1, m - 7)]
        t = time.time()
        ok, _ = check_board(pts, m)
        fam.append({'width': m, 'points': len(pts), 'valid': ok, 'rectangles': len(rects(m)),
                    'seconds': round(time.time() - t, 2)})
    out['collar_family'] = fam
    out['collar_family_all_valid'] = all(f['valid'] for f in fam)
    out['collar_family_widths'] = [8, 120]

    # 6. Model lists of the optimum counts: validity, size, distinctness.
    lists = {}
    for name in ['five_row_optima_structured_w8_cadical153.json', 'five_row_optima_structured_w9_cadical153.json',
                 'five_row_optima_structured_w10_cadical153.json', 'five_row_optima_unstructured_w8_glucose4.json',
                 'five_row_optima_unstructured_w9_glucose4.json', 'five_row_optima_unstructured_w10_glucose4.json']:
        try:
            d = load(name)
        except FileNotFoundError:
            lists[name] = 'missing'
            continue
        m = max(c for mod in d['models'] for c, r in mod['points'])
        ms = []
        bad = 0
        for mod in d['models']:
            ok, bm = check_board(mod['points'], m)
            if not ok or len(mod['points']) != m + 6:
                bad += 1
            ms.append(bm)
        lists[name] = {'width': m, 'models': len(ms), 'distinct': len(set(ms)), 'invalid_or_wrong_size': bad,
                       'complete_flag': d.get('complete')}
    for name in ['five_row_structured_counts_cadical153.json', 'five_row_column_counts_glucose4.json']:
        d = load(name)
        per = []
        for inst in d['instances']:
            m = inst['width']
            mods = inst.get('models_one_based') or []
            ms = []
            bad = 0
            for pts in mods:
                ok, bm = check_board(pts, m)
                if not ok or len(pts) != m + 6:
                    bad += 1
                ms.append(bm)
            per.append({'width': m, 'partition': inst.get('partition_rows_one_based'),
                        'models_found': inst.get('models_found'), 'models_listed': len(ms),
                        'distinct': len(set(ms)), 'invalid_or_wrong_size': bad,
                        'count_exhausted': inst.get('count_exhausted'), 'status': inst.get('status')})
        lists[name] = per
    out['model_lists'] = lists
    out['total_seconds'] = round(time.time() - t0, 1)
    with open(os.path.join(DATA, 'five_row_witness_check.json'), 'w') as f:
        json.dump(out, f, indent=1)
    print('sat witnesses valid:', out['sat_witnesses_all_valid'], len(witnesses))
    print('m+6 widths:', out['m_plus_6_witness_widths'], out['m_plus_6_witnesses_by_source'])
    print('all m+6 witnesses K23:', out['m_plus_6_all_K23'])
    print('quoted:', out['quoted_boards'])
    print('staircase all valid:', out['staircase_all_valid'])
    print('width8 optima:', out['width8_optima'])
    print('family all valid 8..120:', out['collar_family_all_valid'])
    for k, v in lists.items():
        if isinstance(v, list):
            print(k, [(p['width'], p['partition'], p['models_found'], p['models_listed'], p['distinct'],
                       p['invalid_or_wrong_size'], p['count_exhausted']) for p in v])
        else:
            print(k, v)
    print('seconds', out['total_seconds'])


if __name__ == '__main__':
    main()
