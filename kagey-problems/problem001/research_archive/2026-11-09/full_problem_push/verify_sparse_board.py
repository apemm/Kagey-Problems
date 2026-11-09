"""Exact independent verification by completing every pair of black points.

Every weak rectangle contains a black pair, either as a side or as a diagonal.
Rectangles with three or more white corners cannot collide with another one.
"""
from itertools import combinations
from math import gcd,isqrt
from pathlib import Path
import hashlib
import json
import sys
import time

HERE=Path(__file__).resolve().parent


def weak_rectangles(h,w,black_points):
    result=set()
    def add(points):
        positions={y*w+x for x,y in points}
        if len(positions)==4:result.add(sum(1<<p for p in positions))
    for A,C in combinations(black_points,2):
        ax,ay=A;cx,cy=C;dx=cx-ax;dy=cy-ay
        # A,C as opposite corners. Enumerate the alternate integer diagonal.
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
        # A,C as adjacent corners. Every integral perpendicular vector is kV.
        g=gcd(abs(dx),abs(dy));vx=-dy//g;vy=dx//g
        lower=-max(h,w);upper=max(h,w)
        for base,v,bound in ((ax,vx,w-1),(cx,vx,w-1),(ay,vy,h-1),(cy,vy,h-1)):
            if v>0:
                lower=max(lower,-(base//v));upper=min(upper,(bound-base)//v)
            elif v<0:
                lower=max(lower,-((base-bound)//v));upper=min(upper,(-base)//v)
        for k in range(lower,upper+1):
            if k:add((A,C,(ax+k*vx,ay+k*vy),(cx+k*vx,cy+k*vy)))
    return result


def main():
    source=HERE/sys.argv[1]
    data=json.loads(source.read_text());h=data['height']
    witness=next(e for e in data['events'] if e.get('status')=='SAT')
    columns=witness['columns_one_based'];w=len(columns)
    points=[(x,r-1) for x,C in enumerate(columns) for r in C]
    B=sum(1<<(y*w+x) for x,y in points);begin=time.monotonic()
    rects=weak_rectangles(h,w,points);presentations={}
    for R in rects:
        white=R&~B
        assert white not in presentations,(presentations.get(white),R)
        presentations[white]=R
    out={'status':'PASS','height':h,'width':w,'black_points':len(points),
         'weak_rectangles':len(rects),'distinct_weak_presentations':len(presentations),
         'seconds':time.monotonic()-begin,'source':source.name,
         'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
    target=source.with_name(source.stem+'_pair_check.json')
    target.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))


if __name__=='__main__':main()
