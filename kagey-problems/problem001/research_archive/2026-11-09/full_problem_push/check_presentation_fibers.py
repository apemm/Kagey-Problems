"""Exhaustively compare the linear fiber factorization to presentations."""
from collections import defaultdict
from itertools import combinations
from pathlib import Path
import json
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles,collision


def setup(rects):
    pair=defaultdict(list);point=defaultdict(list)
    for R in rects:
        cells=[1<<p for p in range(R.bit_length()) if R>>p&1]
        for a,b in combinations(cells,2):pair[a|b].append(R^a^b)
        for a in cells:point[a].append(R^a)
    return [v for v in pair.values() if len(v)>1]+[v for v in point.values() if len(v)>1]+[rects]


def fibers_valid(groups,B):
    for masks in groups:
        seen=False
        for mask in masks:
            if mask&B==mask:
                if seen:return False
                seen=True
    return True


def main():
    began=time.monotonic();records=[]
    for h,w in ((2,2),(3,3),(3,4),(4,4)):
        rects=rectangles(h,w);groups=setup(rects);valid=hidden=0
        for B in range(1<<(h*w)):
            actual=collision(rects,B) is None
            assert fibers_valid(groups,B)==actual,(h,w,B)
            if actual:
                valid+=1
                hidden+=any(R&B==R for R in rects)
        records.append({'height':h,'width':w,'rectangles':len(rects),
                        'blackouts_checked':1<<(h*w),'valid':valid,
                        'valid_with_one_hidden_rectangle':hidden})
    out={'status':'PASS','checks':records,'seconds':time.monotonic()-began}
    (HERE/'presentation_fibers_check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__':main()
