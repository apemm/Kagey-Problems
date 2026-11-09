"""Count complete SAT models and compare to all valid small blackouts."""
from pathlib import Path
import json
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'.runtime'))
sys.path.insert(0,str(HERE.parents[2]))
from pysat.solvers import Solver
from verify_narrow import rectangles,collision
from presentation_fiber_cnf import encode


def main():
    begin=time.monotonic();records=[]
    for h,w,no_hidden in ((2,2,False),(3,3,False),(3,4,False),(4,4,True)):
        rects=rectangles(h,w);clauses,top,info=encode(rects,h*w,no_hidden,parsimonious=True)
        expected={B for B in range(1<<(h*w)) if collision(rects,B) is None}
        seen=set();count=0
        with Solver(name='cadical195',bootstrap_with=clauses) as solver:
            for model in solver.enum_models():
                truth={v for v in model if v>0}
                B=sum(1<<p for p in range(h*w) if p+1 in truth)
                assert B not in seen
                seen.add(B);count+=1
        assert seen==expected
        records.append({'height':h,'width':w,'complete_models':count,
                        'distinct_valid_blackouts':len(expected),**info})
    out={'status':'PASS','checks':records,'seconds':time.monotonic()-begin}
    (HERE/'presentation_fiber_cnf_check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__':main()
