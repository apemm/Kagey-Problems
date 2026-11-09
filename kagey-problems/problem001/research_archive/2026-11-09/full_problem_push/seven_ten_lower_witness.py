"""Find and independently verify an 18-point seven-by-ten board."""
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles as bit_rectangles, collision
from solver.enumerate import rectangles

points=json.loads((HERE/'seven_nine_seventeen_witness.json').read_text())['witness_one_based']
rects=bit_rectangles(7,10)
for inserted in range(1,11):
    shifted={(c+(c>=inserted),r) for c,r in points}
    for row in range(1,8):
        black=shifted|{(inserted,row)}
        mask=sum(1<<((r-1)*10+c-1) for c,r in black)
        if collision(rects,mask) is not None:
            continue
        visible=[R-black for R in rectangles(7,10)]
        assert len(visible)==len(set(visible))
        out={'black_points':18,'rows':7,'columns':10,'verified_rectangles':len(visible),
             'witness_one_based':sorted(black),
             'column_word':','.join(''.join(str(r) for c,r in sorted(black) if c==x)
                                    for x in range(1,11))}
        (HERE/'seven_ten_lower_witness.json').write_text(json.dumps(out,indent=2)+'\n')
        print(json.dumps(out))
        raise SystemExit
raise RuntimeError('No witness in the tested insertion family')
