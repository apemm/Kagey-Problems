"""Collect the checks of the transfer count five_row_optima_dp.py against independent sources:
  four rows: the exported four-row machines (four_row_counts.json) at widths 6..30;
  five rows: complete SAT enumerations (five_row_optima_structured_w*.json, per partition)
             at widths 8..10 and the structured count run at width 11, the window dynamic
             programme row_bound_count_dp.py (through five_row_count_crosscheck.py) at every
             width where it finished, per partition.
Writes five_row_optima_dp_validation.json and prints the table.

Usage: python five_row_dp_validation.py
"""
import glob
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(HERE, '..', 'data')


def dp_results():
    out = {}
    for path in glob.glob(os.path.join(DATA_DIR, 'five_row_optima_dp_*.json')):
        d = json.load(open(path))
        if 'results' not in d:
            continue
        for r in d['results']:
            if r.get('double_columns') or r['singleton_rows_allowed'] != list(range(1, d['height'] + 1)):
                continue
            if r['status'] != 'complete':
                continue
            key = (d['height'], r['width'])
            val = (r['count'], [p['count'] for p in r['per_partition']], r['seconds'], os.path.basename(path))
            out[key] = val
    return out


def main():
    dp = dp_results()
    rows = []
    # four rows: machine counts
    four = json.load(open(os.path.join(DATA_DIR, 'four_row_counts.json')))
    a4 = {int(k): int(v) for k, v in four['a4'].items()}
    for (h, m), (cnt, per, sec, src) in sorted(dp.items()):
        if h != 4 or m not in a4:
            continue
        rows.append({'height': 4, 'width': m, 'transfer_count': cnt, 'reference': a4[m],
                     'reference_source': 'four_row_counts.json (machine dynamic programme)',
                     'agree': cnt == a4[m], 'transfer_seconds': sec})
    # five rows: SAT enumerations (complete only) and the window DP
    sat = {}
    for path in glob.glob(os.path.join(DATA_DIR, 'five_row_optima_structured_w*_cadical153.json')):
        d = json.load(open(path))
        if d.get('complete'):
            sat[d['grid']['cols']] = (d['model_count'], [p['models'] for p in d['partitions']],
                                      os.path.basename(path))
    counts11 = os.path.join(DATA_DIR, 'five_row_structured_counts_cadical153.json')
    window = {}
    for path in glob.glob(os.path.join(DATA_DIR, 'five_row_count_crosscheck_h5_w*.json')):
        d = json.load(open(path))
        if d['status'] == 'complete':
            window[d['width']] = (d['count'], [p['count'] for p in d['per_partition']],
                                  d['seconds'], os.path.basename(path))
    for (h, m), (cnt, per, sec, src) in sorted(dp.items()):
        if h != 5:
            continue
        rec = {'height': 5, 'width': m, 'transfer_count': cnt, 'transfer_per_partition': per,
               'transfer_seconds': sec}
        if m in sat:
            rec['sat_enumeration_count'] = sat[m][0]
            rec['sat_enumeration_per_partition'] = sat[m][1]
            rec['sat_agrees'] = (sat[m][0] == cnt and sat[m][1] == per)
        if m in window:
            rec['window_dp_count'] = window[m][0]
            rec['window_dp_per_partition'] = window[m][1]
            rec['window_dp_seconds'] = window[m][2]
            rec['window_dp_agrees'] = (window[m][0] == cnt and window[m][1] == per)
        rec['row_reflection_symmetric'] = (per == [per[9], per[8], per[6], per[3], per[7], per[5], per[2], per[4], per[1], per[0]])
        rows.append(rec)
    payload = {'description': 'validation of five_row_optima_dp.py against independent counts',
               'partition_order': 'two-row side of the 2+3 partition: {1,2},{1,3},{1,4},{1,5},{2,3},{2,4},{2,5},{3,4},{3,5},{4,5} (one-based rows)',
               'rows': rows}
    with open(os.path.join(DATA_DIR, 'five_row_optima_dp_validation.json'), 'w') as f:
        json.dump(payload, f, indent=1)
    for r in rows:
        print(r['height'], r['width'], r['transfer_count'],
              'machine' if 'reference' in r else '',
              r.get('agree', ''), 'sat', r.get('sat_agrees', '-'), 'window', r.get('window_dp_agrees', '-'),
              'sym', r.get('row_reflection_symmetric', ''))


if __name__ == '__main__':
    main()
