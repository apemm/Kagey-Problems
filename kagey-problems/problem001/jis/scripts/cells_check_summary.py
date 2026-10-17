"""Collect the independent-check results for the small cells and six rows into
jis/data/cells_check_summary.json: the SAT runs (whole instances and row splits),
the structured six-row SAT runs, the exhaustive six-row DFS runs, the witness
recheck, the periodic recheck and the solver interrupt test.

Usage: python cells_check_summary.py
Coordinates in every collected file are one-based (column, row).
"""
import glob
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, '..', 'data')
CHK = os.path.join(DATA, 'cells_check')


def load(pattern):
    out = []
    for path in sorted(glob.glob(os.path.join(CHK, pattern))):
        if path.endswith('.log'):
            continue
        try:
            d = json.load(open(path))
        except Exception as exc:  # unfinished or killed job without a file
            d = {'file': os.path.basename(path), 'status': 'unreadable: %s' % exc}
        d['file'] = os.path.basename(path)
        out.append(d)
    return out


def main():
    summary = {'coordinates': 'one-based (column,row), (1,1) top-left'}
    sat = load('sat_[0-9]x*.json')
    cells = {}
    for r in sat:
        if 'rows' not in r:
            continue
        key = f"{r['rows']}x{r['cols']}"
        cells.setdefault(key, {}).setdefault(str(r['bound']), []).append(
            {'solver': r['solver'], 'rowcase': r.get('rowcase'), 'status': r['status'],
             'variables': r.get('variables'), 'clauses': r.get('clauses'),
             'encode_seconds': r.get('encode_seconds'), 'solve_seconds': r.get('solve_seconds'),
             'wall_seconds': r.get('wall_seconds'), 'witness': r.get('witness'),
             'witness_valid_by_triples': r.get('witness_valid_by_triples')})
    verdicts = {}
    for key, bounds in cells.items():
        v = {}
        for b, runs in bounds.items():
            whole = [x for x in runs if x['rowcase'] is None]
            cases = [x for x in runs if x['rowcase'] is not None]
            v[b] = {'whole': [(x['solver'], x['status']) for x in whole],
                    'split_cases': sorted((x['rowcase'], x['status']) for x in cases),
                    'split_complete_unsat': bool(cases) and all(x['status'] == 'UNSAT' for x in cases),
                    'any_sat': any(x['status'] == 'SAT' for x in runs)}
        verdicts[key] = v
    summary['small_cells'] = {'runs': cells, 'verdicts': verdicts}

    dfs = load('dfs_w*.json')
    by_width = {}
    for r in dfs:
        by_width.setdefault(r['width'], []).append(
            {'partition_one_based_rows': r.get('partition_one_based_rows'), 'status': r['status'],
             'witnesses_total': r.get('witnesses_total'), 'nodes': r.get('nodes'), 'seconds': r.get('seconds')})
    summary['six_row_dfs'] = {str(w): {'partitions_run': len(v), 'all_finished': all(x['status'] == 'finished' for x in v),
                                       'witnesses_total': sum(x['witnesses_total'] or 0 for x in v),
                                       'nodes': sum(x['nodes'] or 0 for x in v), 'runs': v}
                              for w, v in sorted(by_width.items())}

    ssat = load('ssat_w*.json')
    by_width = {}
    for r in ssat:
        by_width.setdefault(r['width'], []).append(
            {'partition_one_based_rows': r.get('partition_one_based_rows'), 'partition_index': r.get('partition_index'),
             'status': r['status'], 'solver': r['solver'], 'variables': r.get('variables'), 'clauses': r.get('clauses'),
             'encode_seconds': r.get('encode_seconds'), 'solve_seconds': r.get('solve_seconds'),
             'wall_seconds': r.get('wall_seconds'), 'witness': r.get('witness'),
             'witness_valid_by_triples': r.get('witness_valid_by_triples')})
    summary['six_row_structured_sat'] = {str(w): {'partitions_run': len(v),
                                                  'sat': sum(x['status'] == 'SAT' for x in v),
                                                  'unsat': sum(x['status'] == 'UNSAT' for x in v),
                                                  'unresolved': sum(x['status'] not in ('SAT', 'UNSAT') for x in v),
                                                  'runs': v}
                                         for w, v in sorted(by_width.items())}

    for name in ('cells_witness_check.json',):
        summary['witness_check'] = json.load(open(os.path.join(DATA, name)))
    summary['periodic_check'] = json.load(open(os.path.join(CHK, 'six_row_periodic_check.json')))
    summary['solver_interrupt_check'] = json.load(open(os.path.join(CHK, 'solver_interrupt_check.json')))
    json.dump(summary, open(os.path.join(DATA, 'cells_check_summary.json'), 'w'), indent=1)
    print(json.dumps(summary['small_cells']['verdicts'], indent=1))
    print({w: (v['partitions_run'], v['all_finished'], v['witnesses_total']) for w, v in summary['six_row_dfs'].items()})
    print({w: (v['partitions_run'], v['sat'], v['unsat'], v['unresolved']) for w, v in summary['six_row_structured_sat'].items()})


if __name__ == '__main__':
    main()
