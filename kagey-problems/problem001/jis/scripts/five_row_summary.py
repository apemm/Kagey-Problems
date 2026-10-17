r"""Five rows: collect the SAT, ILP and staircase results and recheck every witness.

Reads the JSON files written by five_row_structured_sat.py, five_row_column_sat.py,
five_row_unstructured_sat.py, five_row_cbc.py and five_row_staircase_witness.py, and
for each width 5..20 records the value of f(5,m) that the methods agree on.  Every
witness of m+6 points is rechecked a third time with the definitional oracle of
solver/brute.py (rectangles found by testing all 4-subsets of points, validity as
injectivity of the presentation map), and its column structure is compared with the
equality theorem (six doubles forming K_{2,3}, singletons elsewhere).

Coordinates are ONE-BASED (column, row) throughout, (1, 1) top left.

Usage:
  python five_row_summary.py --data ../data --out ../data/five_row_results.json
"""
import argparse
import json
import os
import sys
import time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, REPO)
import verify_narrow  # noqa: E402
from solver import brute  # noqa: E402

H = 5


def load(path):
    if os.path.exists(path):
        with open(path) as f:
            return json.load(f)
    return None


def brute_valid(points_one_based, m, cache):
    if m not in cache:
        cache[m] = brute.rectangle_masks(H, m)
    masks, n = cache[m]
    idx = {p: k for k, p in enumerate(brute.grid_points(H, m))}
    S = sum(1 << idx[tuple(p)] for p in points_one_based)
    return brute.valid(S, masks), len(masks)


def structure(points_one_based, m):
    cols = {c: sorted(r for cc, r in points_one_based if cc == c) for c in range(1, m + 1)}
    sizes = sorted(len(v) for v in cols.values())
    doubles = sorted(tuple(v) for v in cols.values() if len(v) == 2)
    rows = set()
    for a, b in doubles:
        rows.add(a)
        rows.add(b)
    # bipartite check: the six pairs must be P x Q with |P| = 2, |Q| = 3
    k23 = False
    for P in combinations(range(1, H + 1), 2):
        Q = tuple(r for r in range(1, H + 1) if r not in P)
        if sorted(tuple(sorted((p, q))) for p in P for q in Q) == doubles:
            k23 = True
    return dict(column_sizes=sizes, doubles=doubles, all_columns_nonempty=min(sizes) >= 1,
                max_column=max(sizes), six_doubles=len(doubles) == 6, doubles_form_K23=k23)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--data', default=os.path.join(HERE, '..', 'data'))
    ap.add_argument('--out', default=None)
    args = ap.parse_args()
    D = args.data
    A = load(os.path.join(D, 'five_row_structured_cadical153.json'))
    B = load(os.path.join(D, 'five_row_column_glucose4.json'))
    U = load(os.path.join(D, 'five_row_unstructured_cadical153.json'))
    U2 = load(os.path.join(D, 'five_row_unstructured_cadical153_w11_12.json'))
    if U and U2:                       # second run of widths 11, 12 without the m+7 instances
        seen = {(i['width'], i['bound']) for i in U['instances'] if i['status'] != 'unresolved'}
        U['instances'] += [i for i in U2['instances'] if (i['width'], i['bound']) not in seen]
    elif U2:
        U = U2
    C = load(os.path.join(D, 'five_row_cbc.json'))
    S = load(os.path.join(D, 'five_row_staircase_witnesses.json'))
    cache = {}
    per_width = {}
    for m in range(5, 21):
        rec = dict(width=m, row_bound=m + 6, methods={})
        if A:
            inst = [i for i in A['instances'] if i['width'] == m]
            if inst:
                st = [i['status'] for i in inst]
                sat = [i for i in inst if i['status'] == 'SAT']
                rec['methods']['A_structured_cadical153'] = dict(
                    statuses=st, wall_seconds=round(sum(i.get('wall_seconds', 0) for i in inst), 1),
                    verdict=('m+6 attained' if sat else
                             'no m+6 blackout' if all(s == 'UNSAT' for s in st) else 'unresolved'),
                    witness=sat[0]['witness_one_based'] if sat else None,
                    witness_valid_by_verify_narrow=sat[0]['witness_valid_by_verify_narrow'] if sat else None,
                    clauses_per_partition=[i.get('clauses') for i in inst],
                    variables=inst[0].get('variables'))
        if B:
            inst = [i for i in B['instances'] if i['width'] == m]
            if inst:
                i = inst[0]
                rec['methods']['B_column_glucose4'] = dict(
                    status=i['status'], wall_seconds=i.get('wall_seconds'),
                    clauses=i.get('clauses'), variables=i.get('variables'),
                    witness=i.get('witness_one_based'),
                    witness_valid_by_verify_narrow=i.get('witness_valid_by_verify_narrow'),
                    witness_valid_by_own_check=i.get('witness_valid_by_own_check'))
        if U:
            inst = [i for i in U['instances'] if i['width'] == m]
            if inst:
                rec['methods']['U_unstructured_cadical153'] = {
                    f'|S|>={i["bound"]}': dict(status=i['status'], wall_seconds=i.get('wall_seconds'),
                                               clauses=i.get('clauses'), variables=i.get('variables'),
                                               witness=i.get('witness_one_based'),
                                               witness_valid_by_verify_narrow=i.get('witness_valid_by_verify_narrow'))
                    for i in inst}
        if C:
            inst = [i for i in C['instances'] if i['width'] == m]
            if inst:
                i = inst[0]
                rec['methods']['CBC_ilp'] = dict(status=i['status'], max_blackout=i.get('max_blackout'),
                                                 solve_seconds=i.get('solve_seconds'),
                                                 witness=i.get('witness_one_based'),
                                                 witness_valid_by_verify_narrow=i.get('witness_valid_by_verify_narrow'))
        if S:
            inst = [i for i in S['instances'] if i['width'] == m]
            if inst:
                i = inst[0]
                rec['staircase_plus_one_witness_m_plus_5'] = dict(
                    exists=i['staircase_plus_one_exists'], boards_tested=i['boards_tested'],
                    witness=i.get('witness_one_based'))
        # third check of every m+6 witness with the definitional oracle
        rechecks = []
        for name, meth in rec['methods'].items():
            cands = []
            if name.startswith('U_'):
                for k, v in meth.items():
                    if v.get('witness') and len(v['witness']) >= m + 6:
                        cands.append((k, v['witness']))
            elif meth.get('witness') and len(meth['witness']) == m + 6:
                cands.append((name, meth['witness']))
            for label, w in cands:
                t0 = time.time()
                ok, nr = brute_valid(w, m, cache)
                rechecks.append(dict(source=label if label != name else name, size=len(w),
                                     valid_by_brute_oracle=ok, brute_rectangles=nr,
                                     seconds=round(time.time() - t0, 1), structure=structure(w, m)))
        rec['m_plus_6_witness_rechecks'] = rechecks
        # value decision
        a = rec['methods'].get('A_structured_cadical123', None) or rec['methods'].get('A_structured_cadical153')
        b = rec['methods'].get('B_column_glucose4')
        votes = []
        if a:
            votes.append(('A', a['verdict']))
        if b:
            votes.append(('B', 'm+6 attained' if b['status'] == 'SAT' else
                          'no m+6 blackout' if b['status'] == 'UNSAT' else 'unresolved'))
        u = rec['methods'].get('U_unstructured_cadical153', {})
        if f'|S|>={m + 6}' in u:
            s6 = u[f'|S|>={m + 6}']['status']
            votes.append(('U', 'm+6 attained' if s6 == 'SAT' else
                          'no m+6 blackout' if s6 == 'UNSAT' else 'unresolved'))
        c = rec['methods'].get('CBC_ilp')
        if c and c['status'] == 'optimal':
            votes.append(('CBC', 'm+6 attained' if c['max_blackout'] == m + 6 else
                          'no m+6 blackout' if c['max_blackout'] == m + 5 else 'other'))
        rec['votes'] = votes
        decided = {v for _, v in votes if v != 'unresolved'}
        if len(decided) == 1 and sum(1 for _, v in votes if v != 'unresolved') >= 2:
            verdict = decided.pop()
            if verdict == 'm+6 attained':
                rec['f'] = m + 6
                rec['status'] = 'established-two-methods'
            else:
                rec['f'] = m + 5
                rec['status'] = ('established-two-methods'
                                 if rec.get('staircase_plus_one_witness_m_plus_5', {}).get('exists')
                                 or m <= 10 else 'upper bound only')
        elif len(decided) == 1:
            rec['f'] = m + 6 if 'attained' in next(iter(decided)) else m + 5
            rec['status'] = 'one-method-only'
        elif len(decided) > 1:
            rec['status'] = 'DISAGREEMENT'
        else:
            rec['status'] = 'unresolved'
        per_width[str(m)] = rec
        print(f"width {m}: f = {rec.get('f')} [{rec['status']}] votes {votes} "
              f"rechecks {[r['valid_by_brute_oracle'] for r in rechecks]}", flush=True)
    out = dict(coordinates='one-based (column,row)', widths=per_width)
    if args.out:
        with open(args.out, 'w') as f:
            json.dump(out, f, indent=1)


if __name__ == '__main__':
    main()
