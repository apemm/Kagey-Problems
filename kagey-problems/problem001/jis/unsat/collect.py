"""Collect results.jsonl, the exporter manifest and the cross-check into unsat_certificates.json,
and copy the CNF files into the repository data folder.

The work folder is UNSAT_WORK (default the current folder), as for pipeline.py. It holds
cnf/manifest.json and cnf/splits.json from unsat_export_cnf.py, crosscheck.json from
unsat_cnf_crosscheck.py, and results.jsonl. The faithfulness argument is read from
faithfulness.txt next to this file. The output goes to jis/data/unsat_certificates.json, the
cell CNFs to jis/data/unsat/ as they are, and the six-row CNFs gzipped.

Usage: python collect.py
"""
import gzip
import hashlib
import json
import os
import shutil
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
W = os.path.abspath(os.environ.get('UNSAT_WORK', os.getcwd()))
REPO = os.path.abspath(os.path.join(HERE, '..', 'data'))
FAITH = open(os.path.join(HERE, 'faithfulness.txt')).read().strip()


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()


def main():
    man = {r['name']: r for r in json.load(open(os.path.join(W, 'cnf', 'manifest.json')))}
    splits = json.load(open(os.path.join(W, 'cnf', 'splits.json')))
    cross = json.load(open(os.path.join(W, 'crosscheck.json')))
    xc = {r['name']: r for r in cross['instances']}
    xs = {r['name']: r for r in cross['splits']}
    solve, check = {}, {}
    for line in open(os.path.join(W, 'results.jsonl')):
        r = json.loads(line)
        if r['step'] == 'solve' and not r.get('reused_proof'):
            solve[r['name']] = r
        elif r['step'] == 'check':
            check[r['name']] = r

    def run_record(name):
        s, c = solve.get(name), check.get(name)
        rec = {'cnf_file_sha256': sha(os.path.join(W, 'cnf', name + '.cnf'))}
        if s:
            rec['solver'] = {k: s[k] for k in ('solver', 'status', 'seconds', 'peak_mb', 'cap_seconds')}
        if c and 'error' not in c:
            rec['proof'] = {'format': 'LRAT (text)', 'bytes': c['proof_bytes'],
                            'sha256': c['proof_sha256'],
                            'kept_outside_repository_as': c['stored']}
            rec['lrat_check'] = c['lrat_check']
            rec['lean_lrat_check'] = c['lean_check']
            rec['certified'] = c['lrat_check']['verified'] and c['lean_check']['verified'] \
                and c['lean_check']['parse_roundtrip_identical']
        else:
            rec['certified'] = False
        return rec

    out_inst = []
    dst = os.path.join(REPO, 'unsat')
    os.makedirs(dst, exist_ok=True)
    for name, m in man.items():
        rec = {'instance': name, 'claim': m['claim'], 'variables': m['variables'],
               'clauses': m['clauses'], 'clause_set_sha256': m['clause_set_sha256'],
               'second_generator_identical': xc[name]['identical_clause_sets']}
        src = os.path.join(W, 'cnf', name + '.cnf')
        if name.startswith('cell_'):
            shutil.copyfile(src, os.path.join(dst, name + '.cnf'))
            rec['repository_file'] = f'jis/data/unsat/{name}.cnf'
        else:
            with open(src, 'rb') as a, gzip.GzipFile(os.path.join(dst, name + '.cnf.gz'), 'wb', mtime=0) as b:
                shutil.copyfileobj(a, b)
            rec['repository_file'] = f'jis/data/unsat/{name}.cnf.gz'
        if m.get('split'):
            parts = []
            for p in splits[name]['parts']:
                pr = run_record(p['name'])
                pr = {'part': p['name'], 'units': p['units'], 'clause_set_sha256': p['clause_set_sha256'], **pr}
                parts.append(pr)
            rec['split'] = {'by': splits[name]['split'], 'parts': len(parts),
                            'covering_checked_by_second_generator': xs[name]['patterns_cover_all'],
                            'parts_certified': sum(p['certified'] for p in parts),
                            'solver_seconds_total': round(sum(p.get('solver', {}).get('seconds', 0) for p in parts), 1),
                            'proof_bytes_total': sum(p.get('proof', {}).get('bytes', 0) for p in parts),
                            'part_records': parts}
            rec['certified'] = all(p['certified'] for p in parts) and xs[name]['patterns_cover_all']
        else:
            rec.update(run_record(name))
        out_inst.append(rec)
    shutil.copyfile(os.path.join(W, 'cnf', 'splits.json'), os.path.join(dst, 'splits.json'))
    sixparts = cross['six_row_partitions']
    doc = {
        'description': 'LRAT certificates for the SAT unsatisfiability results of Section 9.',
        'coordinates': 'one-based (column,row), (1,1) top left; variable of zero-based (x,y) is y*m+x+1',
        'generator': 'jis/scripts/unsat_export_cnf.py; second generator jis/scripts/unsat_cnf_crosscheck.py',
        'solver': 'CaDiCaL 2.1.2 (the cadical.exe of the Lean 4.33.1 toolchain), --lrat --binary=false',
        'checkers': {
            'lrat_check': 'lrat-check.c of github.com/marijnheule/drat-trim (master, sha256 '
                          'bf07c2ac96b9035da1ebcc578cb95e956a2b795629d613154cdb307f8a8f4a95), '
                          'compiled unmodified with the toolchain clang 22.1.4 -O2 against a minimal '
                          'header file for the C runtime calls it uses',
            'lean_lrat_check': 'Std.Tactic.BVDecide.LRAT.check of Lean 4.33.1 (soundness theorem '
                               'LRAT.check_sound), run as a compiled executable after a renumbering '
                               'of clause ids; the parsed CNF is written back and compared byte for '
                               'byte with the input. This is a native-execution check: it trusts '
                               'the verified checker, the compiler and the DIMACS parser.'},
        'faithfulness': FAITH,
        'six_row_partitions_complete': sixparts,
        'second_generator_all_agree': cross['all_agree'],
        'instances': out_inst,
    }
    with open(os.path.join(REPO, 'unsat_certificates.json'), 'w') as fh:
        json.dump(doc, fh, indent=1)
    for r in out_inst:
        print(r['instance'], r['certified'], r.get('split', {}).get('parts_certified', ''))


if __name__ == '__main__':
    main()
