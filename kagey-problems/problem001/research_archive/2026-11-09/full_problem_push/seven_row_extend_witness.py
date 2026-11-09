"""Find a one-column extension and verify every rectangle independently."""
from itertools import combinations
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles as bit_rectangles,collision
from solver.enumerate import rectangles

source=json.loads((HERE/sys.argv[1]).read_text())
points=source['witness_one_based']
w=source['columns']+1
added=int(sys.argv[2]) if len(sys.argv)>2 else 1
rects=bit_rectangles(7,w)
attempts=0
for inserted in range(1,w+1):
    shifted={(c+(c>=inserted),r) for c,r in points}
    for rows in combinations(range(1,8),added):
        attempts+=1
        black=shifted|{(inserted,r) for r in rows}
        mask=sum(1<<((r-1)*w+c-1) for c,r in black)
        if collision(rects,mask) is not None:continue
        visible=[R-black for R in rectangles(7,w)]
        assert len(visible)==len(set(visible))
        out={'status':'found','rows':7,'columns':w,'black_points':len(black),
             'attempts':attempts,'verified_rectangles':len(visible),
             'witness_one_based':sorted(black),
             'column_word':','.join(''.join(str(r) for c,r in sorted(black) if c==x)
                                    for x in range(1,w+1))}
        (HERE/f'seven_row_lower_w{w}_b{len(black)}.json').write_text(json.dumps(out,indent=2)+'\n')
        print(json.dumps(out));raise SystemExit
print(json.dumps({'status':'no_witness_in_tested_family','columns':w,'added_points':added,'attempts':attempts}))
