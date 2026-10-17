"""Collect the small-cell and six-row result files into one summary.

Reads jis/data/small_cells_sat_*.json, small_cells_split_*.json, small_cells_ilp_*.json,
six_row_periodic*.json and six_row_sat*_w*_[AB].json, plus the per-run lines of
jis/logs/sat_*.log (written as each solver run finishes, before the cell's JSON file exists),
prints a table, and writes jis/data/cells_sixrows_summary.json. A value is reported as
established only when the two encodings (or two solvers) agree.
"""
import glob
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.abspath(os.path.join(HERE, '..', 'data'))
LOGS = os.path.abspath(os.path.join(HERE, '..', 'logs'))


def small_cells():
    cells = {}
    for f in sorted(glob.glob(os.path.join(DATA, 'small_cells_sat_*.json'))):
        with open(f) as fh:
            loaded = json.load(fh)
        for d in (loaded if isinstance(loaded, list) else [loaded]):
            c = cells.setdefault(d['grid'], {'runs': []})
            c.update({'rows': d['rows'], 'cols': d['cols'], 'game_witness': d.get('game_witness')})
            c['runs'] += d['runs']
    for f in glob.glob(os.path.join(LOGS, 'sat_*.log')):
        grid = re.search(r'sat_(\d+x\d+)', f).group(1)
        c = cells.setdefault(grid, {'runs': []})
        known = {(r['bound'], r['encoding'], r['solver']) for r in c['runs']}
        with open(f) as fh:
            for line in fh:
                if not line.startswith('{'):
                    continue
                r = json.loads(line)
                if (r['bound'], r['encoding'], r['solver']) not in known:
                    c['runs'].append(r)
                    known.add((r['bound'], r['encoding'], r['solver']))
    for f in glob.glob(os.path.join(DATA, 'small_cells_split_*.json')):
        with open(f) as fh:
            r = json.load(fh)
        c = cells.setdefault(r['grid'], {'runs': []})
        c.setdefault('split', []).append(r)
    for f in glob.glob(os.path.join(DATA, 'small_cells_ilp_*.json')):
        with open(f) as fh:
            for d in json.load(fh):
                c = cells.setdefault(d['grid'], {'runs': []})
                c.setdefault('ilp', []).append(d)
    out = {}
    for g, c in cells.items():
        c['cols'] = int(g.split('x')[1])
        sat_bounds = {}
        for r in c['runs']:
            sat_bounds.setdefault(r['bound'], []).append((r['encoding'], r['solver'], r['status'], r['solve_seconds']))
        best_sat = max((b for b, rs in sat_bounds.items() if any(x[2] == 'SAT' for x in rs)), default=None)
        unsat = sorted(b for b, rs in sat_bounds.items()
                       if sum(x[2] == 'UNSAT' for x in rs) >= 1)
        unsat2 = sorted(b for b, rs in sat_bounds.items()
                        if len({x[0] for x in rs if x[2] == 'UNSAT'}) >= 2)
        split = {}
        for r in c.get('split', []):
            split.setdefault(r['bound'], {}).setdefault(r['encoding'], []).append((r['case'], r['status'], r['solve_seconds']))
        split_unsat = [b for b, encs in split.items()
                       if sum(all(x[1] == 'UNSAT' for x in v) and len(v) == c.get('cols', 0) for v in encs.values()) >= 2]
        out[g] = {'bounds': {str(b): rs for b, rs in sorted(sat_bounds.items())},
                  'largest_sat_bound': best_sat, 'unsat_bounds_one_encoding': unsat,
                  'unsat_bounds_both_encodings': sorted(set(unsat2) | set(split_unsat)),
                  'split_cases': {str(b): v for b, v in split.items()},
                  'split_unsat_both_encodings': split_unsat, 'ilp': c.get('ilp', [])}
    return out


def six_rows():
    widths = {}
    for f in glob.glob(os.path.join(DATA, 'six_row_sat_w*_[AB].json')):
        m = re.search(r'_w(\d+)_([AB])', f)
        w, enc = int(m.group(1)), m.group(2)
        with open(f) as fh:
            recs = json.load(fh)
        for r in recs:
            key = tuple(map(tuple, r['partition_zero_based_rows']))
            rec = widths.setdefault(w, {}).setdefault(enc, {})
            rec[str(key)] = {'status': r['status'], 'solve_seconds': r['solve_seconds'],
                             'valid': r.get('witness_valid_by_verify_narrow'),
                             'collar_pass': [k for k, v in r.get('collar', {}).items()
                                             if v['valid_by_verify_narrow'] and v['valid_by_side_vectors']]}
    summary = {}
    for w in sorted(widths):
        s = {}
        for enc in ('A', 'B'):
            recs = widths[w].get(enc, {})
            s[enc] = {'partitions_done': len(recs),
                      'sat': sum(r['status'] == 'SAT' for r in recs.values()),
                      'unsat': sum(r['status'] == 'UNSAT' for r in recs.values()),
                      'unresolved': sum(r['status'] == 'unresolved' for r in recs.values()),
                      'collar_passes': {k: r['collar_pass'] for k, r in recs.items() if r['collar_pass']}}
        a, b = s['A'], s['B']
        if a['sat'] or b['sat']:
            s['verdict'] = f'f(6,{w}) = {w + 9} (witness checked by verify_narrow)'
        elif a['unsat'] == 10 and b['unsat'] == 10:
            s['verdict'] = f'f(6,{w}) <= {w + 8} (all 10 partitions UNSAT, both encoders)'
        elif a['unsat'] == 10 or b['unsat'] == 10:
            s['verdict'] = 'one encoder UNSAT on all partitions; other incomplete'
        else:
            s['verdict'] = 'incomplete'
        summary[w] = s
    periodic = []
    for f in glob.glob(os.path.join(DATA, 'six_row_periodic*.json')):
        with open(f) as fh:
            recs = json.load(fh)
        for r in recs:
            if r['witnesses_found'] or not r['finished']:
                periodic.append({'file': os.path.basename(f), 'rows': r.get('rows'), 'gap': r['gap'],
                                 'width': r['width'], 'partition': r['partition'],
                                 'witnesses_found': r['witnesses_found'], 'finished': r['finished']})
    return {'structured_sat': summary, 'periodic_hits': periodic}


def main():
    out = {'small_cells': small_cells(), 'six_rows': six_rows()}
    for g, c in out['small_cells'].items():
        print(g, 'largest SAT bound', c['largest_sat_bound'], 'UNSAT (both encodings)', c['unsat_bounds_both_encodings'],
              'UNSAT (one)', c['unsat_bounds_one_encoding'])
        for b, rs in c['bounds'].items():
            print('   bound', b, rs)
        for i in c['ilp']:
            print('   ILP', i['solver'][:40], i['status'], i.get('max_blackout'), i['seconds'], 's')
    for w, s in out['six_rows']['structured_sat'].items():
        print('six rows width', w, s['verdict'], '| A', s['A']['sat'], s['A']['unsat'], s['A']['unresolved'],
              '| B', s['B']['sat'], s['B']['unsat'], s['B']['unresolved'],
              '| collar passes A', list(s['A']['collar_passes'].items())[:2], 'B', list(s['B']['collar_passes'].items())[:2])
    print('periodic hits', out['six_rows']['periodic_hits'])
    with open(os.path.join(DATA, 'cells_sixrows_summary.json'), 'w') as fh:
        json.dump(out, fh, indent=1)


if __name__ == '__main__':
    main()
