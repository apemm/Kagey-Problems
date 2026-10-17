"""Recheck every witness quoted in the small-cell and six-row result files with the
right-angle-triple enumerator of cells_common_check.py.

For each six-row witness the column structure (every column one or two black
points, the nine doubles carrying the nine K_{3,3} edges of the stated partition)
and the collar boards are rebuilt from the witness points alone, never from the
stored collar points, and the collar verdicts are compared with the stored ones.
Also checks the three witnesses quoted verbatim in the summary and, as a test of
the collar theorem's prediction, the width-16 witness with 8..40 row-1 singleton
columns appended.

Coordinates: one-based (column, row), (1,1) top left.  Output:
jis/data/cells_witness_check.json.
"""
import glob
import json
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from cells_common_check import rectangles_by_triples, first_collision  # noqa: E402

DATA = os.path.join(HERE, '..', 'data')
W6 = 7  # W_h = 1 + floor((h-1)^2/4) for h = 6

RECTS = {}


def rects(rows, cols):
    if (rows, cols) not in RECTS:
        RECTS[rows, cols] = rectangles_by_triples(rows, cols)
    return RECTS[rows, cols]


def check_board(rows, cols, points):
    pts = {tuple(p) for p in points}
    assert len(pts) == len(points), 'repeated point'
    assert all(1 <= c <= cols and 1 <= r <= rows for c, r in pts), 'point off the grid'
    col = first_collision(rects(rows, cols), pts)
    return col is None, (None if col is None else [sorted(col[0]), sorted(col[1])])


def six_row_structure(width, points, partition_one_based):
    """Return (ok, double_columns, min_gap) for a claimed m+9 witness."""
    cols = {}
    for c, r in points:
        cols.setdefault(c, set()).add(r)
    side_a, side_b = (set(partition_one_based[0]), set(partition_one_based[1]))
    edges = set()
    doubles = []
    for c in range(1, width + 1):
        rs = cols.get(c, set())
        if len(rs) == 1:
            continue
        if len(rs) != 2:
            return False, [], None
        a, b = sorted(rs)
        if not ((a in side_a and b in side_b) or (a in side_b and b in side_a)):
            return False, [], None
        if (a, b) in edges:
            return False, [], None
        edges.add((a, b))
        doubles.append(c)
    ok = len(doubles) == 9 and len(edges) == 9
    gaps = [doubles[i + 1] - doubles[i] for i in range(len(doubles) - 1)]
    return ok, doubles, (min(gaps) if gaps else None)


def collar_board(width, points, key):
    """Rebuild a collar board from the witness points: key is rowR_side with R in
    {1,6} and side in {left,right,both}; W6 singleton columns in row R per side."""
    m = re.fullmatch(r'row([16])_(left|right|both)', key)
    row, side = int(m.group(1)), m.group(2)
    shift = W6 if side in ('left', 'both') else 0
    pts = {(c + shift, r) for c, r in points}
    new_width = width + shift + (W6 if side in ('right', 'both') else 0)
    if side in ('left', 'both'):
        pts |= {(c, row) for c in range(1, W6 + 1)}
    if side in ('right', 'both'):
        pts |= {(c, row) for c in range(new_width - W6 + 1, new_width + 1)}
    return new_width, pts


def main():
    t0 = time.time()
    out = {'coordinates': 'one-based (column,row), (1,1) top-left',
           'enumerator': 'right-angle corner triples (cells_common_check.py)',
           'small_cells': [], 'six_rows': [], 'collars': [], 'periodic': [],
           'quoted_witnesses': [], 'extended_collar': [], 'problems': []}

    # --- small cells -------------------------------------------------------
    for path in sorted(glob.glob(os.path.join(DATA, 'small_cells_sat_*.json'))):
        d = json.load(open(path))
        rows, cols = d['rows'], d['cols']
        entry = {'file': os.path.basename(path), 'rows': rows, 'cols': cols,
                 'rectangles_by_triples': len(rects(rows, cols)),
                 'rectangles_reported': d.get('rectangles_verify_narrow'), 'witnesses': []}
        boards = []
        if d.get('game_witness'):
            boards.append(('game', d['game_witness']['points'], d['game_witness']['size']))
        for run in d['runs']:
            if run.get('witness'):
                boards.append((f"bound {run['bound']} {run['encoding']}/{run['solver']}", run['witness'], run['bound']))
        for label, pts, size in boards:
            ok, col = check_board(rows, cols, pts)
            entry['witnesses'].append({'source': label, 'size': len(pts), 'claimed_size_or_bound': size,
                                       'valid': ok, 'collision': col})
            if not ok or len(pts) < size:
                out['problems'].append((os.path.basename(path), label))
        out['small_cells'].append(entry)

    # --- six rows: every SAT witness, structure, collars ---------------------
    for path in sorted(glob.glob(os.path.join(DATA, 'six_row_sat_w*_[AB].json'))):
        d = json.load(open(path))
        for e in d:
            if e['status'] != 'SAT':
                continue
            width = e['width']
            part = [[r + 1 for r in side] for side in e['partition_zero_based_rows']]
            pts = [tuple(p) for p in e['witness']]
            ok, col = check_board(6, width, pts)
            sok, doubles, mingap = six_row_structure(width, pts, part)
            rec = {'file': os.path.basename(path), 'width': width, 'partition_one_based_rows': part,
                   'size': len(pts), 'target': e['target'], 'valid': ok, 'structure_ok': sok,
                   'double_columns': doubles, 'min_double_gap': mingap}
            if not ok or not sok or len(pts) != width + 9:
                out['problems'].append((os.path.basename(path), width, part))
            out['six_rows'].append(rec)
            for key, info in (e.get('collar') or {}).items():
                nw, cpts = collar_board(width, pts, key)
                cok, ccol = check_board(6, nw, cpts)
                claimed = info.get('valid_by_verify_narrow')
                out['collars'].append({'file': os.path.basename(path), 'width': width,
                                       'partition_one_based_rows': part, 'collar': key,
                                       'board_width': nw, 'size': len(cpts),
                                       'rectangles_by_triples': len(rects(6, nw)),
                                       'valid_rebuilt': cok, 'valid_claimed': claimed,
                                       'agree': cok == claimed})
                if cok != claimed:
                    out['problems'].append((os.path.basename(path), width, part, key, 'collar disagreement'))

    # --- periodic witnesses ---------------------------------------------------
    for e in json.load(open(os.path.join(DATA, 'six_row_periodic.json'))):
        for w in e['witnesses']:
            pts = [tuple(p) for p in w['points']]
            ok, col = check_board(6, e['width'], pts)
            out['periodic'].append({'gap': e['gap'], 'width': e['width'], 'partition_zero_based': e['partition'],
                                    'size': len(pts), 'valid': ok})
            if not ok:
                out['problems'].append(('periodic', e['gap'], w['edge_order_zero_based_rows']))

    # --- the three witnesses quoted verbatim in the summary -----------------
    quoted = {
        '6x8 15 points': (6, 8, [(1, 1), (1, 5), (2, 1), (3, 1), (3, 2), (3, 3), (4, 3), (4, 4), (5, 4), (6, 4),
                                 (7, 4), (7, 5), (7, 6), (8, 2), (8, 6)]),
        '6x15 24 points': (6, 15, [(1, 5), (1, 6), (2, 4), (2, 5), (3, 3), (3, 4), (4, 2), (4, 3), (5, 1), (6, 1),
                                   (7, 1), (7, 4), (8, 1), (9, 1), (10, 1), (10, 2), (11, 3), (11, 6), (12, 1),
                                   (13, 2), (13, 5), (14, 6), (15, 1), (15, 6)]),
        '6x16 25 points': (6, 16, [(1, 3), (1, 6), (2, 1), (2, 4), (3, 2), (3, 5), (4, 6), (5, 6), (6, 1), (6, 6),
                                   (7, 6), (8, 6), (9, 5), (9, 6), (10, 4), (10, 5), (11, 4), (12, 4), (13, 4),
                                   (14, 3), (14, 4), (15, 2), (15, 3), (16, 1), (16, 2)]),
    }
    for label, (rows, cols, pts) in quoted.items():
        ok, col = check_board(rows, cols, pts)
        rec = {'label': label, 'size': len(pts), 'valid': ok, 'collision': col}
        if rows == 6 and cols >= 15:
            sok, doubles, mingap = six_row_structure(cols, pts, [[1, 3, 5], [2, 4, 6]])
            rec.update({'structure_ok_for_135_246': sok, 'double_columns': doubles, 'min_double_gap': mingap})
        out['quoted_witnesses'].append(rec)
        if not ok:
            out['problems'].append(('quoted', label))
    # the 6 x 23 collar board of the width-16 witness, and all six collar keys
    w16 = quoted['6x16 25 points'][2]
    for key in ('row1_right', 'row1_left', 'row1_both', 'row6_right', 'row6_left', 'row6_both'):
        nw, cpts = collar_board(16, w16, key)
        ok, col = check_board(6, nw, cpts)
        out['quoted_witnesses'].append({'label': f'6x16 witness collar {key}', 'board_width': nw,
                                        'size': len(cpts), 'rectangles_by_triples': len(rects(6, nw)),
                                        'valid': ok})
    # the theorem's prediction: 8..40 appended row-1 singleton columns stay valid
    for k in range(8, 41):
        pts = set(w16) | {(c, 1) for c in range(17, 17 + k)}
        ok, col = check_board(6, 16 + k, pts)
        out['extended_collar'].append({'appended': k, 'board_width': 16 + k, 'size': len(pts), 'valid': ok})
        if not ok:
            out['problems'].append(('extended collar', k))

    out['seconds'] = round(time.time() - t0, 1)
    json.dump(out, open(os.path.join(DATA, 'cells_witness_check.json'), 'w'), indent=1)
    print('witness boards:', len(out['small_cells']), 'small-cell files,', len(out['six_rows']), 'six-row witnesses,',
          len(out['collars']), 'collar boards,', len(out['periodic']), 'periodic witnesses')
    print('problems:', out['problems'])
    print('seconds', out['seconds'])


if __name__ == '__main__':
    main()
