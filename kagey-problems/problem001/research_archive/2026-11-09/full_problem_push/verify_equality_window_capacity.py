"""Independently check restricted row-core catalogs and completed SAT coverage.

No SAT instances are run. An incomplete width-fourteen run is reported as such.
"""
from itertools import combinations
from pathlib import Path
import hashlib
import json
import time

HERE = Path(__file__).resolve().parent


def reflection(mask):
    return sum(1 << (6-r) for r in range(7) if mask >> r & 1)


def independent_balanced_ten_catalog():
    edges = list(combinations(range(7), 2))
    result = {}
    raw = 0
    for selected in combinations(range(21), 10):
        neighbors = [0]*7
        for index in selected:
            a,b = edges[index]
            neighbors[a] |= 1 << b
            neighbors[b] |= 1 << a
        color = [-1]*7
        color[0] = 0
        stack = [0]
        good = True
        while stack and good:
            a = stack.pop()
            bits = neighbors[a]
            while bits:
                bit = bits & -bits
                bits -= bit
                b = bit.bit_length()-1
                if color[b] < 0:
                    color[b] = 1-color[a]
                    stack.append(b)
                elif color[b] == color[a]:
                    good = False
                    break
        if not good or -1 in color or sorted((color.count(0),color.count(1))) != [3,4]:
            continue
        raw += 1
        core = tuple(sorted((1 << edges[j][0]) | (1 << edges[j][1]) for j in selected))
        full = tuple(sorted((1 << a) | (1 << b) for a in range(7) for b in range(a+1,7)
                            if color[a] != color[b]))
        image = tuple(sorted(map(reflection,core)))
        if image < core:
            core = image
            full = tuple(sorted(map(reflection,full)))
        assert core not in result or result[core] == full
        result[core] = full
    assert raw == 2310 and len(result) == 1164
    return result


def load_completed(pattern, width, target):
    solved = {}
    sources = []
    for path in sorted(HERE.glob(pattern)):
        data = json.loads(path.read_text())
        assert data.get('height',data.get('rows')) == 7, path.name
        assert data.get('width',data.get('columns')) == width, path.name
        assert data['target'] == target, path.name
        results = data.get('results', [])
        if not results:
            continue
        ids = [r['index'] for r in results]
        assert ids[0] == data['start_index'], path.name
        assert ids[-1] < data['end_exclusive'], path.name
        assert ids == list(range(ids[0], ids[-1]+1)), path.name
        for record in results:
            assert record['status'] in ('SAT','UNSAT'), path.name
            index,status = record['index'],record['status']
            assert index not in solved or solved[index] == status, (path.name,index)
            solved[index] = status
        sources.append(dict(name=path.name, sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                            first_index=ids[0], last_index=ids[-1]))
    return solved,sources


def main():
    began = time.monotonic()
    cores13 = json.loads((HERE/'fixed_excess_ten_cores.json').read_text())['cores']
    needed13 = {i for i,record in enumerate(cores13)
                if max(mask.bit_count() for mask in record['masks']) == 2}
    assert len(needed13) == 1707
    solved13,sources13 = load_completed('fixed_core_h7_w13_*cadical195*.json',13,23)
    assert all(solved13.get(i) == 'UNSAT' for i in needed13)

    independent = independent_balanced_ten_catalog()
    records14 = json.loads((HERE/'equality_window14_cores.json').read_text())['cores']
    actual = {tuple(r['masks']):tuple(r['full_masks']) for r in records14}
    assert actual == independent and all(r['empty_columns'] == 0 for r in records14)
    solved14,sources14 = load_completed('equality_window14_*_cadical195.json',14,24)
    complete14 = all(solved14.get(i) == 'UNSAT' for i in range(1164))
    out = dict(status='PASS', no_triple_width13_upper=22,
               no_triple_width13_cores=1707, width13_sources=sources13,
               balanced_width14_raw_cores=2310, balanced_width14_reflection_cores=1164,
               width14_completed_unsat=sum(solved14.get(i)=='UNSAT' for i in range(1164)),
               width14_sat_indices=[i for i in range(1164) if solved14.get(i)=='SAT'],
               width14_complete_unsat=complete14,
               final_F_width14_double_capacity=9 if complete14 else None,
               seven_row_equality_width_lower_bound=17 if complete14 else 16,
               width14_sources=sources14, seconds=time.monotonic()-began)
    (HERE/'equality_window_capacity_check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if not k.endswith('_sources')}))


if __name__ == '__main__':
    main()
