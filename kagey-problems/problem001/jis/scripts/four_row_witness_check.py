"""Recheck of the stored four-row optimum witnesses with an independent presentation test.

Every witness listed in the four-row direct-enumeration files (one-based
(column, row) points) is tested from the definition: the rectangles of the
4 x m grid are generated from right-angle triples, and the blackout is valid
when the map rectangle -> visible corners is injective.  The point count must
be m + 4 and the four double columns must carry the row pairs of the named
partition.  The result goes to jis/data/four_row_witness_check.json.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from four_row_direct_check import DATA, PARTITIONS, rectangles_by_triples  # noqa: E402

FILES = {'four_row_direct_flat.json': 'first_witness_per_partition',
         'four_row_direct_dfs.json': 'first_witness_per_partition',
         'four_row_direct_check_full.json': 'samples',
         'four_row_direct_check_structured.json': 'samples'}
KEYS = {'01|23': '{1,2}|{3,4}', '02|13': '{1,3}|{2,4}', '03|12': '{1,4}|{2,3}'}


def valid(points_one_based, cols):
    pts = {(c - 1, r - 1) for c, r in points_one_based}
    assert all(0 <= x < cols and 0 <= y < 4 for x, y in pts)
    seen = set()
    for rect in rectangles_by_triples(4, cols):
        visible = frozenset(rect - pts)
        if visible in seen:
            return False
        seen.add(visible)
    return True


def partition_name(points_one_based):
    cols = {}
    for c, r in points_one_based:
        cols.setdefault(c, set()).add(r - 1)
    doubles = sorted(tuple(sorted(s)) for s in cols.values() if len(s) == 2)
    if any(len(s) > 2 for s in cols.values()) or len(doubles) != 4:
        return None
    for name, (left, right) in PARTITIONS.items():
        if doubles == sorted(tuple(sorted((a, b))) for a in left for b in right):
            return name
    return None


def main():
    out = {}
    total = 0
    for fname, key in FILES.items():
        path = os.path.join(DATA, fname)
        if not os.path.exists(path):
            continue
        d = json.load(open(path))
        entries = d['results'] if 'results' in d else list(d.values())
        checks = []
        for e in entries:
            cols = e['width']
            for pname, pts in (e.get(key) or {}).items():
                name = KEYS.get(pname, pname)
                ok = valid(pts, cols) and len(pts) == cols + 4 and partition_name(pts) == name
                checks.append({'width': cols, 'partition': name, 'points': len(pts), 'valid': ok})
                total += 1
        out[fname] = {'witnesses': len(checks), 'all_valid': all(c['valid'] for c in checks),
                      'details': checks}
        print(fname, len(checks), 'witnesses, all valid:', out[fname]['all_valid'])
    out['total_witnesses'] = total
    json.dump(out, open(os.path.join(DATA, 'four_row_witness_check.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()
