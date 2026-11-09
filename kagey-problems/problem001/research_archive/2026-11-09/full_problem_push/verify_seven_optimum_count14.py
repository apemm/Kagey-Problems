"""Independent catalogs, reflection weights, and actual presentations for a_7(14)."""
from collections import defaultdict
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
import json
import time

HERE = Path(__file__).resolve().parent
H, W = 7, 14

def reflect_mask(mask):
    return sum(1 << (6-r) for r in range(7) if mask >> r & 1)

def canon(core):
    core = tuple(sorted(core))
    return min(core,tuple(sorted(map(reflect_mask,core))))

def reflect_board(black,hflip=False,vflip=False):
    return sum(1 << ((6-r if vflip else r)*W+(W-1-c if hflip else c))
               for r in range(H) for c in range(W) if black >> (r*W+c) & 1)

def columns(black):
    return [sum(1 << r for r in range(H) if black >> (r*W+c) & 1)
            for c in range(W)]

def main():
    began = time.monotonic()
    pairs = list(combinations(range(H),2))
    pair_index = {pair:i for i,pair in enumerate(pairs)}
    pair_masks = [(1 << a)|(1 << b) for a,b in pairs]
    triangle_masks = [sum(1 << pair_index[p] for p in combinations(triple,2))
                      for triple in combinations(range(H),3)]
    ten = set()
    for edges in combinations(range(21),10):
        edge_bits = sum(1 << i for i in edges)
        if any(edge_bits & tri == tri for tri in triangle_masks):
            continue
        ten.add(canon(pair_masks[i] for i in edges))
    assert len(ten) == 1497
    triples = set()
    raw_triples = set()
    full = set()
    eleven = set()
    for part in combinations(range(H),3):
        left = set(part)
        complete = tuple(sorted((1 << a)|(1 << b)
                                for a in left for b in range(H) if b not in left))
        full.add(canon(complete))
        for omitted in complete:
            eleven.add(canon(e for e in complete if e != omitted))
        outside = sorted(set(range(H))-left)
        # Equality in the four-row outside Mantel bound gives a K_2,2.
        for side in combinations(outside,2):
            other = set(outside)-set(side)
            edges = [(a,b) for a in side for b in other]
            for colors in product(part,repeat=4):
                attachment = dict(zip(outside,colors))
                if any(attachment[a] == attachment[b] for a,b in edges):
                    continue
                core = tuple(sorted([sum(1 << r for r in part)]
                                    + [(1 << a)|(1 << b) for a,b in edges]
                                    + [(1 << r)|(1 << attachment[r]) for r in outside]))
                raw_triples.add(core)
                triples.add(canon(core))
    assert len(raw_triples) == 1890 and len(triples) == 957
    assert len(eleven) == 210 and len(full) == 19
    expected = sorted([(c,0) for c in ten|triples] + [(c,1) for c in eleven])
    catalog = json.loads((HERE/'fixed_excess_ten_cores.json').read_text())['cores']
    actual = [(tuple(r['masks']),r['empty_columns']) for r in catalog]
    assert expected == actual and len(actual) == 2664
    two_manifest = json.loads((HERE/'seven_fourteen_two_empty_manifest.json').read_text())
    assert sorted(full) == [tuple(c) for c in two_manifest['cores']]
    two_records = [json.loads(s) for s in
                   (HERE/'seven_fourteen_two_empty_count.jsonl').read_text().splitlines()]
    assert len(two_records) == 19
    assert sorted(r['index'] for r in two_records) == list(range(19))
    assert all(r['status'] == 'complete' and not r['models']
               and r['weighted_count'] == 0 for r in two_records)

    records = []
    names = [f'excess_ten_count_w14_shard{i}.jsonl' for i in (0,1)]
    for name in names:
        records.extend(json.loads(s) for s in (HERE/name).read_text().splitlines())
    assert len(records) == 2664
    assert sorted(r['index'] for r in records) == list(range(2664))
    all_boards = set()
    weighted = 0
    projected = []
    positive_cores = []
    for record in records:
        assert record['status'] == 'complete'
        assert record['width'] == W and record['target'] == 24
        core,empty = actual[record['index']]
        vr = 1 if tuple(sorted(map(reflect_mask,core))) == core else 2
        assert record['vertical_weight'] == vr
        assert len(record['models']) == len(set(record['models']))
        subtotal = 0
        for encoded in record['models']:
            black = int(encoded,16)
            masks = columns(black)
            assert black.bit_count() == 24
            assert tuple(sorted(m for m in masks if m.bit_count() >= 2)) == core
            assert masks.count(0) == empty
            assert masks.index(core[0]) < 7
            subtotal += 2*vr
            projected.append(dict(index=record['index'],black=encoded,weight=2*vr))
            for hf,vf in product((False,True),repeat=2):
                all_boards.add(reflect_board(black,hf,vf))
        assert subtotal == record['weighted_count']
        weighted += subtotal
        if record['models']:
            positive_cores.append(record['index'])
    assert weighted == len(all_boards) == 80
    diagonal_groups = defaultdict(list)
    cells = [(c,r,r*W+c) for r in range(H) for c in range(W)]
    for (x,y,p),(u,v,q) in combinations(cells,2):
        diagonal_groups[(x+u,y+v,(x-u)**2+(y-v)**2)].append((p,q))
    rectangles = set()
    for ds in diagonal_groups.values():
        for first,second in combinations(ds,2):
            vertices = set(first+second)
            assert len(vertices) == 4
            rectangles.add(sum(1 << p for p in vertices))
    boards = []
    for black in sorted(all_boards):
        presentations = {rectangle & ~black for rectangle in rectangles}
        assert len(presentations) == len(rectangles)
        masks = columns(black)
        for length,bound in {9:17,10:18,11:20,12:21,13:23}.items():
            assert max(sum(m.bit_count() for m in masks[i:i+length])
                       for i in range(W-length+1)) <= bound
        boards.append(dict(black=hex(black),
                           column_word=','.join(''.join(str(r+1) for r in range(H)
                                                      if mask >> r & 1) or '-'
                                                for mask in masks),
                           presentations=len(presentations),
                           hidden_rectangles=int(0 in presentations)))
    source_names = ['count_seven_excess_ten.py','fixed_row_core_sat.py',
                    'seven_row_equality_sat.py','fixed_excess_ten_cores.json',
                    'count_seven_fourteen_two_empty.py',
                    'seven_fourteen_two_empty_manifest.json',
                    'seven_fourteen_two_empty_count.jsonl',
                    'verify_seven_optimum_count14.py'] + names
    result = dict(status='PASS',height=H,width=W,optimum=24,optimum_count=80,
                  catalog_families=dict(ten_doubles=1497,triple_and_eight_doubles=957,
                                        eleven_doubles_one_empty=210,
                                        twelve_doubles_two_empty=19),
                  completed_primary_cores=2664,completed_two_empty_cores=19,
                  positive_core_indices=sorted(positive_cores),
                  projected_model_count=len(projected),projected_models=projected,
                  rectangles=len(rectangles),boards=boards,
                  seconds=time.monotonic()-began,
                  source_sha256={name:sha256((HERE/name).read_bytes()).hexdigest()
                                 for name in source_names},
                  scope='Independent complete core generation, symmetry expansion, '
                        'and actual presentation checks; exhaustion relies on SAT records.')
    (HERE/'seven_optimum_count14_independent_check.json').write_text(
        json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()
                      if k not in ('boards','projected_models','source_sha256')},indent=2))

if __name__ == '__main__':
    main()
