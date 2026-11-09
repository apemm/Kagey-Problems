"""Independent pair-completion verification, excluding automatic axis pairs.

The input must have one singleton per ordinary column and every parity double
exactly once. Axis uniqueness is then structural. Generate every tilted
rectangle with two black points independently of the SAT shape compiler.
"""
from itertools import combinations
from math import gcd,isqrt
from pathlib import Path
import hashlib
import json
import sys
import time

HERE=Path(__file__).resolve().parent


def tilted_pairs(h,w,points):
    seen=set()
    def add(corners):
        if len(set(corners))!=4:return
        if len({x for x,y in corners})==2 and len({y for x,y in corners})==2:return
        seen.add(tuple(sorted(y*w+x for x,y in corners)))
    for A,C in combinations(points,2):
        ax,ay=A;cx,cy=C;dx=cx-ax;dy=cy-ay
        if ay==cy and ay in (0,h-1):continue
        sx=ax+cx;sy=ay+cy;square=dx*dx+dy*dy
        for by in range(h):
            remain=square-(2*by-sy)**2
            if remain<0:continue
            root=isqrt(remain)
            if root*root!=remain:continue
            for delta in {root,-root}:
                if (sx+delta)%2:continue
                bx=(sx+delta)//2;ex=sx-bx;ey=sy-by
                if 0<=bx<w and 0<=ex<w and 0<=ey<h:add((A,C,(bx,by),(ex,ey)))
        if not dx or not dy:continue
        g=gcd(abs(dx),abs(dy));vx=-dy//g;vy=dx//g
        lower=-max(h,w);upper=max(h,w)
        for base,v,bound in ((ax,vx,w-1),(cx,vx,w-1),(ay,vy,h-1),(cy,vy,h-1)):
            if v>0:
                lower=max(lower,-(base//v));upper=min(upper,(bound-base)//v)
            else:
                lower=max(lower,-((base-bound)//v));upper=min(upper,(-base)//v)
        for k in range(lower,upper+1):
            if k:add((A,C,(ax+k*vx,ay+k*vy),(cx+k*vx,cy+k*vy)))
    return seen


def check(h,cols):
    w=len(cols)
    assert all(1<=len(C)<=2 for C in cols)
    assert all(0<=r<h for C in cols for r in C)
    doubles=[tuple(sorted(C)) for C in cols if len(C)==2]
    expected={(a,b) for a,b in combinations(range(h),2) if (a-b)%2}
    assert len(doubles)==len(expected) and set(doubles)==expected
    points=[(x,r) for x,C in enumerate(cols) for r in C]
    black={r*w+x for x,r in points}
    rects=tilted_pairs(h,w,points);presentations={}
    for R in rects:
        P=tuple(p for p in R if p not in black)
        assert P and P not in presentations,('hidden_or_duplicate',R,P)
        presentations[P]=R
        if len(P)==1:
            x,r=P[0]%w,P[0]//w
            assert not any((r-s)%2 for s in cols[x]),('singleton_axis_rival',R)
        else:
            assert len(P)==2
            x,r=P[0]%w,P[0]//w;z,s=P[1]%w,P[1]//w
            if x==z:assert not (r-s)%2,('vertical_axis_rival',R)
            elif r==s:assert not cols[x]&cols[z],('horizontal_axis_rival',R)
            else:assert not (s in cols[x] and r in cols[z]),('oblique_axis_rival',R)
    return {'height':h,'width':w,'black_points':len(points),'parity_doubles':len(doubles),
            'weak_tilted_rectangles':len(rects),'distinct_tilted_presentations':len(presentations)}


def calibrate():
    from verify_sparse_board import weak_rectangles
    checked=0
    for name in ('constant_sea_h7_cadical195_seed17.json','constant_sea_h9_cadical195_seed17_free1.json'):
        data=json.loads((HERE/name).read_text());h=data['height']
        cols=[{r-1 for r in C} for C in next(e for e in data['events'] if e.get('status')=='SAT')['columns_one_based']]
        w=len(cols);points=[(x,r) for x,C in enumerate(cols) for r in C]
        old=set()
        for mask in weak_rectangles(h,w,points):
            corners=[]
            while mask:
                b=mask&-mask;corners.append(b.bit_length()-1);mask-=b
            if len({p%w for p in corners})==2 and len({p//w for p in corners})==2:continue
            old.add(tuple(sorted(corners)))
        assert old==tilted_pairs(h,w,points)
        check(h,cols);checked+=1
    return checked


def main():
    begin=time.monotonic();source=HERE/sys.argv[1]
    data=json.loads(source.read_text());h=data['height']
    columns=next(e for e in data['events'] if e.get('status')=='SAT')['columns_one_based']
    out=check(h,[set(r-1 for r in C) for C in columns])
    out.update(status='PASS',source=source.name,source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
               calibration_boards=calibrate(),seconds=time.monotonic()-begin)
    (HERE/(source.stem+'_tilted_pair_check.json')).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__':main()
