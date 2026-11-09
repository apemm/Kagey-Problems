"""Independent equal-diagonal check of the four-column full-box exception."""
from itertools import product
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles,axis_rectangles


def main():
    h=8;w=4;part={1,2,3,6};phase=(0,1,1,0)
    allowed=[tuple(r for r in range(1,h+1) if int(r in part)==s) for s in phase]
    axis=set(axis_rectangles(h,w));tilted=[R for R in rectangles(h,w) if R not in axis]
    checked=0
    for word in product(*allowed):
        black=sum(1<<((r-1)*w+x) for x,r in enumerate(word))
        for R in tilted:
            white=[p for p in range(h*w) if (R&~black)>>p&1]
            if len(white)==1:
                p=white[0];x=p%w;r=p//w+1
                assert int(r in part)==phase[x]
            elif len(white)==2 and white[0]%w==white[1]%w:
                r,s=(p//w+1 for p in white)
                assert (r in part)==(s in part)
        checked+=1
    coloring=tuple(int(r in part) for r in range(1,h+1))
    assert all(coloring!=tuple((k*(r*(r-1)//2)+a*r+b)%2 for r in range(1,h+1))
               for k,a,b in product(range(2),repeat=3))
    out={'status':'PASS','height':h,'width':w,'one_class':sorted(part),'phase':phase,
         'cartesian_assignments_checked':checked,'tilted_rectangles_per_assignment':len(tilted),
         'scope':'singleton-axis and vertical-pair axis rivals only',
         'row_coloring_is_not_ordinary_or_quadratic':True}
    (HERE/'finite_full_box_width4_independent_check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__':main()
