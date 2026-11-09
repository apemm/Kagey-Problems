"""Independent catalog, symmetry, and diagonal-geometry check of a_7(21)."""
from collections import defaultdict
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
H, W = 7, 21
BOUNDS = {9:17, 10:18, 11:20, 12:21, 13:23, 14:24, 15:25,
          16:26, 17:27, 18:29, 19:30, 20:31}

def reflect_mask(mask):
    return sum(1 << (6-r) for r in range(7) if mask >> r & 1)

def reflect_board(black, horizontal=False, vertical=False):
    result = 0
    for r in range(H):
        for c in range(W):
            if black >> (r*W+c) & 1:
                result |= 1 << ((H-1-r if vertical else r)*W
                                + (W-1-c if horizontal else c))
    return result

def columns(black):
    return [sum(1 << r for r in range(H) if black >> (r*W+c) & 1)
            for c in range(W)]

def main():
    raw = set()
    for part in combinations(range(H), 3):
        left = set(part)
        raw.add(tuple(sorted((1 << a) | (1 << b)
                             for a in left for b in range(H) if b not in left)))
    assert len(raw) == 35
    representatives = sorted({min(core, tuple(sorted(map(reflect_mask, core))))
                              for core in raw})
    assert len(representatives) == 19
    manifest = json.loads((HERE/'seven_fourteen_two_empty_manifest.json').read_text())
    assert [list(c) for c in representatives] == manifest['cores']
    records = [json.loads(line) for line in
               (HERE/'equality_optimum_count_w21.jsonl').read_text().splitlines()]
    assert len(records) == 19
    assert sorted(r['index'] for r in records) == list(range(19))
    all_boards = set()
    weighted_count = 0
    model_records = []
    for record in records:
        core = representatives[record['index']]
        assert record['status'] == 'complete'
        assert record['width'] == W and record['target'] == W+12
        assert tuple(record['core']) == core
        vr = 1 if tuple(sorted(map(reflect_mask, core))) == core else 2
        assert record['vertical_weight'] == vr
        subtotal = 0
        assert len(record['models']) == len(set(record['models']))
        for encoded in record['models']:
            black = int(encoded, 16)
            masks = columns(black)
            assert black.bit_count() == 33
            assert all(mask.bit_count() in (1,2) for mask in masks)
            assert tuple(sorted(m for m in masks if m.bit_count() == 2)) == core
            anchor = masks.index(core[0])
            assert anchor < (W+1)//2
            hr = 1 if anchor == W//2 else 2
            subtotal += hr*vr
            for hflip in (False, True):
                for vflip in (False, True):
                    all_boards.add(reflect_board(black,hflip,vflip))
            model_records.append(dict(index=record['index'],black=encoded,
                                      anchor_column=anchor+1,
                                      horizontal_weight=hr,vertical_weight=vr))
        assert subtotal == record['weighted_count']
        weighted_count += subtotal
    assert weighted_count == 4 and len(all_boards) == 4
    assert len(model_records) == 2 and {r['index'] for r in model_records} == {12}

    # Every rectangle is exactly a pair of equal-length diagonals with one midpoint.
    diagonal_groups = defaultdict(list)
    cells = [(c,r,r*W+c) for r in range(H) for c in range(W)]
    for (x,y,p),(u,v,q) in combinations(cells,2):
        diagonal_groups[(x+u,y+v,(x-u)**2+(y-v)**2)].append((p,q))
    rectangles = set()
    for diagonals in diagonal_groups.values():
        for first,second in combinations(diagonals,2):
            vertices = frozenset(first+second)
            assert len(vertices) == 4
            rectangles.add(sum(1 << p for p in vertices))
    verified = []
    for black in sorted(all_boards):
        presentations = set()
        hidden = 0
        for rectangle in rectangles:
            presentation = rectangle & ~black
            assert presentation not in presentations
            presentations.add(presentation)
            hidden += presentation == 0
        assert hidden == 0
        masks = columns(black)
        for length,bound in BOUNDS.items():
            assert max(sum(m.bit_count() for m in masks[start:start+length])
                       for start in range(W-length+1)) <= bound
        word = ','.join(''.join(str(r+1) for r in range(H) if mask >> r & 1)
                        for mask in masks)
        verified.append(dict(black=hex(black),column_word=word,
                             presentations=len(presentations),hidden_rectangles=hidden))
    source_files = ['count_seven_equality_optima.py','fixed_row_core_sat.py',
                    'seven_row_equality_sat.py','equality_optimum_count_w21.jsonl',
                    'seven_fourteen_two_empty_manifest.json',
                    'verify_seven_equality_count21.py']
    result = dict(status='PASS',height=H,width=W,optimum=33,optimum_count=4,
                  raw_balanced_cores=35,reflection_cores=19,
                  completed_core_indices=list(range(19)),
                  projected_models=model_records,rectangles=len(rectangles),
                  verified_boards=verified,
                  source_sha256={name:sha256((HERE/name).read_bytes()).hexdigest()
                                 for name in source_files},
                  scope='Independent catalog, symmetry, and actual presentation check; '
                        'exhaustive absence relies on the completed SAT enumerations.')
    (HERE/'seven_equality_count21_independent_check.json').write_text(
        json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
