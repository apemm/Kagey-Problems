"""Find and independently verify a 17-point seven-by-nine board."""
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
PROBLEM=HERE.parents[2]
sys.path.insert(0,str(PROBLEM))
import verify_narrow
from solver.enumerate import rectangles


def main():
    source=PROBLEM/'jis/data/table_counts/sat_7x8_16.json'
    models=json.loads(source.read_text())[0]['first_models']
    rects=verify_narrow.rectangles(7,9)
    attempts=0
    for points in models:
        for inserted in range(1,10):
            shifted={(c+(c>=inserted),r) for c,r in points}
            for row in range(1,8):
                attempts+=1
                black=shifted|{(inserted,row)}
                mask=sum(1<<((r-1)*9+c-1) for c,r in black)
                if verify_narrow.collision(rects,mask) is not None:
                    continue
                allrects=rectangles(7,9)
                visible=[R-black for R in allrects]
                assert len(visible)==len(set(visible))
                out={'black_points':17,'rows':7,'columns':9,
                     'attempts':attempts,'verified_rectangles':len(allrects),
                     'witness_one_based':sorted(black),
                     'column_word':','.join(''.join(str(r) for c,r in sorted(black) if c==x)
                                            for x in range(1,10))}
                (HERE/'seven_nine_seventeen_witness.json').write_text(json.dumps(out,indent=2)+'\n')
                print(json.dumps(out))
                return
    raise RuntimeError('No witness in the tested insertion family')


if __name__=='__main__':
    main()
