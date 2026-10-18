"""Recount of a_4(m) from the exported four-row machines, written from scratch.

For each balanced row partition the archive exports a geometry machine over
the eight column letters (four singleton masks 1, 2, 4, 8 and the four double
masks of the partition's row pairs; a mask bit r is zero-based row r).  State
0 is the empty prefix, every listed state accepts, -1 is rejection.  A word of
m columns is a maximum blackout of the 4 x m grid (m >= 6) exactly when the
machine accepts it and each of the four doubles occurs once.

This script builds the product of the machine with the register of used
doubles, lists the reachable product states by breadth-first search, and runs
the exact integer count column by column.  It writes a_4(m) and the three
partition counts for 0 <= m <= WIDTH to jis/data/four_row_dp_check.json and
compares them with jis/data/four_row_counts.json.

Usage: python four_row_dp_check.py [WIDTH]   (default 1500)
"""
import json
import os
import sys
import time
from pathlib import Path

HERE = os.path.dirname(os.path.abspath(__file__))
PROBLEM = os.path.dirname(os.path.dirname(HERE))
DATA = os.path.join(PROBLEM, 'jis', 'data')
MACHINE_DIR = Path(__file__).resolve().parent.parent / 'data' / 'four_row_machines'
MACHINES = {'{1,2}|{3,4}': 'machine_56910.json',
            '{1,3}|{2,4}': 'machine_36912.json',
            '{1,4}|{2,3}': 'machine_351012.json'}
PARTITION_ROWS = {'{1,2}|{3,4}': ((0, 1), (2, 3)),
                  '{1,3}|{2,4}': ((0, 2), (1, 3)),
                  '{1,4}|{2,3}': ((0, 3), (1, 2))}


def load_machine(name):
    with open(MACHINE_DIR / MACHINES[name]) as f:
        m = json.load(f)
    alphabet = m['alphabet']
    left, right = PARTITION_ROWS[name]
    edges = sorted((1 << a) | (1 << b) for a in left for b in right)
    assert alphabet[:4] == [1, 2, 4, 8] and sorted(alphabet[4:]) == edges, name
    trans = m['transitions']
    assert len(trans) == m['state_count']
    return alphabet, trans


def product_automaton(alphabet, trans):
    """Reachable states (U, s) of the machine times the used-double register, as edge lists."""
    S = len(trans)
    start = 0  # U = 0, s = 0
    key = lambda U, s: U * S + s
    seen = {start}
    frontier = [start]
    edges = []
    while frontier:
        nxt = []
        for k in frontier:
            U, s = divmod(k, S)
            for i, letter in enumerate(alphabet):
                t = trans[s][i]
                if t < 0:
                    continue
                if i >= 4:
                    d = i - 4
                    if U >> d & 1:
                        continue
                    nu = U | (1 << d)
                else:
                    nu = U
                k2 = key(nu, t)
                edges.append((k, k2))
                if k2 not in seen:
                    seen.add(k2)
                    nxt.append(k2)
        frontier = nxt
    reachable = sorted(seen)
    index = {k: i for i, k in enumerate(reachable)}
    accepting = [index[k] for k in reachable if k // S == 15]
    edge_idx = [(index[a], index[b]) for a, b in edges]
    return len(reachable), len(accepting), accepting, edge_idx, index[start]


def count_sequence(alphabet, trans, width):
    n, n_acc, accepting, edges, start = product_automaton(alphabet, trans)
    cur = [0] * n
    cur[start] = 1
    seq = [sum(cur[i] for i in accepting)]
    for _ in range(width):
        new = [0] * n
        for a, b in edges:
            new[b] += cur[a]
        cur = new
        seq.append(sum(cur[i] for i in accepting))
    return seq, n, n_acc


def main():
    width = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
    t0 = time.time()
    per = {}
    info = {}
    for name in MACHINES:
        alphabet, trans = load_machine(name)
        seq, n, n_acc = count_sequence(alphabet, trans, width)
        per[name] = seq
        info[name] = {'geometry_states': len(trans), 'reachable_product_states': n,
                      'reachable_accepting_states': n_acc}
    total = [sum(per[name][m] for name in per) for m in range(width + 1)]
    out = {'description': 'a_4(m) = number of maximum blackouts of the 4 x m grid, m >= 6; '
                          'zero for m <= 5 (no equality word exists there)',
           'method': 'exact integer count on the product of each archive machine with the '
                     'used-double register, reachable states by breadth-first search',
           'width': width, 'product_automata': info,
           'a4': {str(m): str(v) for m, v in enumerate(total)},
           'per_partition': {name: {str(m): str(v) for m, v in enumerate(seq)}
                             for name, seq in per.items()},
           'seconds': round(time.time() - t0, 2)}
    cmp_path = os.path.join(DATA, 'four_row_counts.json')
    if os.path.exists(cmp_path):
        other = json.load(open(cmp_path))
        names = {'01|23': '{1,2}|{3,4}', '02|13': '{1,3}|{2,4}', '03|12': '{1,4}|{2,3}'}
        mism = []
        for m in range(min(width, other['max_width']) + 1):
            if int(other['a4'][str(m)]) != total[m]:
                mism.append(('a4', m))
            for k, name in names.items():
                if int(other['per_partition'][k][str(m)]) != per[name][m]:
                    mism.append((name, m))
        out['comparison_with_four_row_counts'] = {
            'widths_compared': min(width, other['max_width']) + 1,
            'mismatches': mism[:10], 'agree': not mism}
    json.dump(out, open(os.path.join(DATA, 'four_row_dp_check.json'), 'w'), indent=1)
    print('product automata:', info)
    print('a4(6..12):', total[6:13])
    print('per partition at 8..10:', {k: v[8:11] for k, v in per.items()})
    print('comparison:', out.get('comparison_with_four_row_counts'))
    print('seconds', out['seconds'])


if __name__ == '__main__':
    main()
