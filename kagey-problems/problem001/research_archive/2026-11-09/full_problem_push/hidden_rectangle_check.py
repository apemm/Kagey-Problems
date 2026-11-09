"""Independent finite check of the hidden-rectangle theorem and sharpness."""
from pathlib import Path
import json
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles,collision


def main():
    begin=time.monotonic()
    results=[]
    for h in range(4,9):
        for w in range(h,9):
            rects=rectangles(h,w)
            supports=set()
            for i,R in enumerate(rects):
                for T in rects[:i]:
                    if (R&T).bit_count()==2:
                        supports.add(R^T)
            assert all(R in supports for R in rects)
            results.append({'rows':h,'columns':w,'rectangles':len(rects),
                            'each_rectangle_is_a_four_point_collision_support':True})
    sharp=[]
    for w in range(3,13):
        rects=rectangles(3,w)
        for center in range(1,w-1):
            black=sum(1<<(r*w+c) for c,r in
                      ((center-1,1),(center,0),(center+1,1),(center,2)))
            assert collision(rects,black) is None
            assert sum(R&black==R for R in rects)==1
        sharp.append({'rows':3,'columns':w,'verified_centers':w-2})
    out={'status':'passed','large_boards':results,'height_three_examples':sharp,
         'elapsed_seconds':time.monotonic()-begin}
    (HERE/'hidden_rectangle_check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__':
    main()
