"""SHA-256 manifest of the evidence files behind the computer-assisted results.

The groups below name, for each result of the inventory in README.md, the stored files that
record it. The hash of a text file is taken after replacing CRLF by LF, so it equals the hash of
the file as committed to git on every platform; gzip files are hashed as they are.

Usage (from kagey-problems/problem001):
    python jis/scripts/evidence_manifest.py --print    print the hash block of README.md
    python jis/scripts/evidence_manifest.py --check    compare the files with README.md
--check exits 1 if a file is missing or its hash differs from the one in README.md.
"""
import glob
import hashlib
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))          # kagey-problems/problem001
README = os.path.join(HERE, 'README.md')
D = 'jis/data/'

GROUPS = [
    ('R1 three rows', [D + 'three_row_closed_form.json', D + 'three_row_closed_form_check.json',
                       D + 'three_row_definition_check.json', D + 'three_row_formula_check.json',
                       D + 'three_row_orbits.json', D + 'three_row_symmetry_check.json',
                       D + 'three_row_reference/*.json']),
    ('R2 four rows, small widths', [D + 'four_row_direct_flat.json', D + 'four_row_direct_dfs.json',
                                    D + 'four_row_direct_check_full.json',
                                    D + 'four_row_direct_check_structured.json',
                                    D + 'four_row_witness_check.json',
                                    D + 'four_row_equivalence_check.json',
                                    D + 'four_row_machines/*.json']),
    ('R3 four rows, generating function and growth', [
        D + 'four_row_counts.json.gz', D + 'four_row_dp_check.json.gz',
        D + 'four_row_recurrence.json', D + 'four_row_recurrence_check.json',
        D + 'four_row_window_check.json', D + 'four_row_rho_check.json',
        D + 'four_row_root_isolation.json', D + 'four_row_growth_check.json']),
    ('R4 five rows, part (a)', [D + 'five_row_structured_cadical153.json',
                                D + 'five_row_column_glucose4.json',
                                D + 'five_row_unstructured_cadical153.json',
                                D + 'five_row_sat_check.json',
                                D + 'five_row_unstructured_dfs_check.json',
                                D + 'five_row_results.json']),
    ('R5 five rows, part (b)', [D + 'five_row_collar_family_w8_row1_right.json',
                                D + 'five_row_family_brute_check.json',
                                D + 'five_row_geometry_check.json']),
    ('R6 five rows, part (c) and the counts', [
        D + 'five_row_width8_candidates.json', D + 'five_row_structured_counts_cadical153.json.gz',
        D + 'five_row_column_counts_glucose4.json', D + 'five_row_count_dfs_check.json',
        D + 'five_row_count_dfs_check_w12.json', D + 'five_row_count_crosscheck_h5_w*.json',
        D + 'five_row_optima_dp_w1[3-9].json', D + 'five_row_optima_dp_w2[0-3].json']),
    ('R7 six rows, part (a)', [D + 'six_row_sat_w9_[AB].json'] +
     [D + 'six_row_sat_w1%d_[AB].json' % w for w in range(0, 5)] +
     [D + 'cells_check/ssat_jobs.json', D + 'cells_check/ssat_jobs_summary.json',
      D + 'cells_check/ssat_w1[3-6]_p*_cadical195.json', D + 'cells_check/dfs_w*_p*.json']),
    ('R8 six rows, part (b)', [D + 'six_row_sat_w15_[AB].json', D + 'six_row_sat_w16_[AB].json',
                               D + 'six_row_sat_w17_[AB].json',
                               D + 'six_row_witness_brute_w15_17.json']),
    ('R9 small grids', [D + 'small_cells_sat_5x6.json', D + 'small_cells_sat_5x7_b12.json',
                        D + 'small_cells_sat_6x6.json', D + 'small_cells_sat_6x7.json',
                        D + 'small_cells_sat_6x8.json', D + 'small_cells_sat_6x8_b16.json',
                        D + 'small_cells_sat_6x8_b17.json', D + 'small_cells_sat_7x7.json',
                        D + 'small_cells_sat_7x7_b16.json', D + 'small_cells_split_7x7_b15_case*.json',
                        D + 'small_cells_ilp_highs.json', D + 'small_cells_ilp_cbc.json',
                        D + 'cells_check/sat_jobs.json', D + 'cells_check/sat_jobs_summary.json',
                        D + 'cells_check/sat_jobs_satcases.json',
                        D + 'cells_check/sat_jobs_satcases_summary.json',
                        D + 'cells_check/sat_[4-7]x*.json', D + 'cells_witness_check.json']),
    ('R10 table counts and f(7,8)', [D + 'table_counts/*.json']),
    ('R11 six rows, widths 9 to 14 (open question)', [D + 'small_cells_sat_6x9_b16.json',
                                                      D + 'six_row_collar_6x9_check.json']),
]


def sha256(path):
    with open(path, 'rb') as fh:
        data = fh.read()
    if not path.endswith('.gz') and b'\0' not in data[:8000]:
        data = data.replace(b'\r\n', b'\n')
    return hashlib.sha256(data).hexdigest()


def files():
    seen = []
    for name, patterns in GROUPS:
        for pat in patterns:
            hits = sorted(glob.glob(os.path.join(ROOT, pat)))
            if not hits:
                raise SystemExit('no file matches %s' % pat)
            for p in hits:
                rel = os.path.relpath(p, ROOT).replace(os.sep, '/')
                if rel not in [r for _, r in seen]:
                    seen.append((name, rel))
    return seen


def block():
    lines = []
    current = None
    for name, rel in files():
        if name != current:
            lines.append('# ' + name)
            current = name
        lines.append('%s  %s' % (sha256(os.path.join(ROOT, rel)), rel))
    return lines


def check():
    with open(README) as fh:
        text = fh.read()
    stored = dict((m.group(2), m.group(1))
                  for m in re.finditer(r'^([0-9a-f]{64})  (\S+)$', text, re.M))
    bad = 0
    present = files()
    present_names = set(rel for _, rel in present)
    for _, rel in present:
        path = os.path.join(ROOT, rel)
        if rel not in stored:
            print('not in README.md:', rel)
            bad += 1
        elif sha256(path) != stored[rel]:
            print('hash differs:', rel)
            bad += 1
    # A file listed in README.md must still exist. The glob patterns above only see the files that
    # are there, so a deleted file would otherwise go unnoticed.
    for rel in sorted(stored):
        if rel not in present_names:
            print('missing:', rel)
            bad += 1
    print('%d files listed, %d found, %d problems' % (len(stored), len(present), bad))
    return 1 if bad else 0


if __name__ == '__main__':
    if '--print' in sys.argv:
        print('\n'.join(block()))
    else:
        sys.exit(check())
