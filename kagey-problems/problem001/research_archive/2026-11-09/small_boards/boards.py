"""Loaders for the stored equality boards. Every board is returned as
(name, height, columns), where columns[x] is the sorted list of black rows
(numbered from 1) of column x. Source files are read, never modified."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PUSH = HERE.parent / 'full_problem_push'
D07 = HERE.parents[1] / '2026-11-07' / 'data'


def from_points(points, width):
    cols = [[] for _ in range(width)]
    for c, r in points:
        cols[c - 1].append(r)
    return [sorted(c) for c in cols]


def last_event_columns(path):
    d = json.loads(Path(path).read_text())
    for e in reversed(d['events']):
        if isinstance(e, dict) and 'columns_one_based' in e:
            return [sorted(c) for c in e['columns_one_based']]
    raise KeyError(path)


def load_all():
    out = []
    d = json.loads((PUSH / 'seven_equality_count21_independent_check.json').read_text())
    for i, b in enumerate(d['verified_boards']):
        out.append((f'h7_w21_{chr(97 + i)}', 7, [[int(ch) for ch in t] for t in b['column_word'].split(',')]))
    d = json.loads((D07 / 'cegar_h11_warm_t3.json').read_text())
    out.append(('h11_w169', 11, [sorted(c) for c in d['cols']]))
    d = json.loads((PUSH / 'height15_width441_coordinates.json').read_text())
    out.append(('h15_w441_oddsea', 15, from_points(d['black_points_one_based'], d['width'])))
    d = json.loads((PUSH / 'height15_width441_binary_coordinates.json').read_text())
    out.append(('h15_w441_binary', 15, from_points(d['black_points_one_based'], d['width'])))
    d = json.loads((PUSH / 'height19_width713_binary_coordinates.json').read_text())
    out.append(('h19_w713_binary', 19, from_points(d['black_points_one_based'], d['width'])))
    return out


def load_extra():
    """Further stored boards used only for the width table and as controls."""
    out = []
    out.append(('h9_w77', 9, last_event_columns(PUSH / 'constant_sea_h9_cadical195_seed18_odd57.json')))
    for name in ('cegar_h11_s4_hyb_t3_111', 'cegar_h11_mod4_j1_t4', 'cegar_h11_mod4_j2_t4'):
        d = json.loads((D07 / f'{name}.json').read_text())
        out.append((f'h11_{name}', 11, [sorted(c) for c in d['cols']]))
    for name, tag in (('constant_sea_h15_cadical195_seed101_high385_s8_mask8', 'h15_w441_mask8'),
                      ('constant_sea_h15_cadical195_seed102_high385_s8_mask10', 'h15_w441_mask10'),
                      ('constant_sea_h15_cadical195_seed103_high385_s8_mask42', 'h15_w441_mask42')):
        out.append((tag, 15, last_event_columns(PUSH / f'{name}.json')))
    return out
