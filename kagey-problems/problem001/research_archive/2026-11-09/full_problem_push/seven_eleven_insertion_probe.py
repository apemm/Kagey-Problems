"""Bounded two-point insertion probe; not an exhaustive upper-bound search."""
from itertools import combinations
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles as bit_rectangles,collision
from solver.enumerate import rectangles

points=json.loads((HERE/'seven_ten_lower_witness.json').read_text())['witness_one_based']
rects=bit_rectangles(7,11)
attempts=0
for inserted in range(1,12):
    shifted={(c+(c>=inserted),r) for c,r in points}
    for rows in combinations(range(1,8),2):
        attempts+=1
        black=shifted|{(inserted,r) for r in rows}
        mask=sum(1<<((r-1)*11+c-1) for c,r in black)
        if collision(rects,mask) is not None:
            continue
        visible=[R-black for R in rectangles(7,11)]
        assert len(visible)==len(set(visible))
        out={'status':'found','black_points':20,'rows':7,'columns':11,
             'attempts':attempts,'verified_rectangles':len(visible),
             'witness_one_based':sorted(black),
             'column_word':','.join(''.join(str(r) for c,r in sorted(black) if c==x)
                                    for x in range(1,12))}
        (HERE/'seven_eleven_insertion_probe.json').write_text(json.dumps(out,indent=2)+'\n')
        print(json.dumps(out))
        raise SystemExit
out={'status':'no_witness_in_tested_family','attempts':attempts}
for inserted in range(1,12):
    shifted={(c+(c>=inserted),r) for c,r in points}
    for row in range(1,8):
        black=shifted|{(inserted,row)}
        mask=sum(1<<((r-1)*11+c-1) for c,r in black)
        if collision(rects,mask) is None:
            visible=[R-black for R in rectangles(7,11)]
            assert len(visible)==len(set(visible))
            out['verified_lower_bound']=19
            out['lower_witness_one_based']=sorted(black)
            out['lower_column_word']=','.join(''.join(str(r) for c,r in sorted(black) if c==x)
                                              for x in range(1,12))
            break
    if 'verified_lower_bound' in out:
        break
(HERE/'seven_eleven_insertion_probe.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
