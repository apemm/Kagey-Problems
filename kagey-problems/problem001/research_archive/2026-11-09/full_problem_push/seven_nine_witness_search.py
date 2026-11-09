"""Bounded 18-point witness search from stored 7x8 witnesses."""
from itertools import combinations
from pathlib import Path
import json
import sys
import time

HERE=Path(__file__).resolve().parent
PROBLEM=HERE.parents[2]
sys.path.insert(0,str(PROBLEM))
import verify_narrow
from solver.enumerate import rectangles as independent_rectangles


def main():
    started=time.monotonic()
    deadline=started+60
    source=PROBLEM/'jis/data/table_counts/sat_7x8_16.json'
    models=json.loads(source.read_text())[0]['first_models']
    rects=verify_narrow.rectangles(7,9)
    attempts=0
    witness=None
    for points in models:
        old_columns=[0]*8
        for x,r in points:
            old_columns[x-1]|=1<<(r-1)
        for x in range(9):
            shifted=old_columns[:x]+[0]+old_columns[x:]
            base=sum(1<<(r*9+c) for c,b in enumerate(shifted)
                     for r in range(7) if b>>r&1)
            old_white=[r*9+c for c in range(9) if c!=x
                       for r in range(7) if not shifted[c]>>r&1]
            new_cells=[r*9+x for r in range(7)]
            choices=list(combinations(new_cells,2))
            choices.extend((a,b) for a in new_cells for b in old_white)
            for added in choices:
                attempts+=1
                black=base|sum(1<<i for i in added)
                assert black.bit_count()==18
                if verify_narrow.collision(rects,black) is None:
                    witness=sorted((i%9+1,i//9+1) for i in range(63) if black>>i&1)
                    break
            if witness or time.monotonic()>deadline:
                break
        if witness or time.monotonic()>deadline:
            break
    out={'status':'found' if witness else 'no_witness_in_tested_family',
         'attempts':attempts,'elapsed_seconds':time.monotonic()-started,
         'witness_one_based':witness}
    if witness:
        points=set(map(tuple,witness))
        seen=set()
        independent=independent_rectangles(7,9)
        for rectangle in independent:
            visible=rectangle-points
            assert visible not in seen
            seen.add(visible)
        out['independent_rectangle_count']=len(independent)
        out['column_word']=','.join(''.join(str(r) for c,r in witness if c==x) for x in range(1,10))
    (HERE/'seven_nine_witness.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out),flush=True)


if __name__=='__main__':
    main()
