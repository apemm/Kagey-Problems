"""Write the six-row instances of width w and target w+8 (encoder A of six_row_excess8_sat.py) as
DIMACS files, for LRAT certification of f(6,w) < w+8 at w = 9, 10, 11.

One file per structural case: six8_w{w}_{family}{index:03d}.cnf, where index is the position
of the case in six_row_excess8_sat.cases() restricted to that family. The clauses are exactly
those that encode_a returns (the full-black at-most-one constraint is pysat's sequential
counter). A manifest lists, per file, the case, the number of variables and clauses, and the
SHA-256 of the file.

Usage: python six_row_excess8_export_cnf.py OUT_DIR WIDTH [WIDTH ...]
"""
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from six_row_excess8_sat import cases, encode_a


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    manifest = []
    for w in map(int, sys.argv[2:]):
        seen = {}
        for family, edges, empty, label in cases():
            k = seen.get(family, 0)
            seen[family] = k + 1
            name = f'six8_w{w}_{family}{k:03d}'
            clauses, n, info = encode_a(w, edges, empty)
            nv = max(abs(l) for c in clauses for l in c)
            text = f'p cnf {nv} {len(clauses)}\n' + ''.join(
                ' '.join(map(str, c)) + ' 0\n' for c in clauses)
            path = os.path.join(out, name + '.cnf')
            with open(path, 'w', newline='\n') as fh:
                fh.write(text)
            manifest.append({'name': name, 'width': w, 'target': w + 8, 'family': family,
                             'case': label, 'zero_based_edges': [list(e) for e in edges],
                             'variables': nv, 'clauses': len(clauses),
                             'sha256': hashlib.sha256(text.encode()).hexdigest()})
            print(name, nv, len(clauses), flush=True)
    with open(os.path.join(out, 'six8_manifest.json'), 'w') as fh:
        json.dump(manifest, fh, indent=1)


if __name__ == '__main__':
    main()
