"""Exact small-height search for a quantitative reflection-closure bound."""
import argparse
from itertools import combinations
import json
from pathlib import Path
import time

def run(h):
    started=time.monotonic()
    odd=sum(1<<j for j in range(0,h,2))
    full=(1<<h)-1
    even=full^odd
    centers=[(k,((1<<(h-2*k))-1)<<k) for k in range(1,(h+1)//2)]
    best=None
    records={}
    checked=0
    for rows in combinations(range(h),h//2):
        a=sum(1<<r for r in rows)
        distance=min((a^odd).bit_count(),(a^even).bit_count())
        if not distance:
            continue
        violations=sum((a & ((a<<k)^(a>>k)) & valid).bit_count()
                       for k,valid in centers)
        previous=records.get(distance)
        if previous is None or violations<previous['violations']:
            records[distance]=dict(distance=distance,violations=violations,
                                   rows=[r+1 for r in rows])
        if best is None or violations*best['distance']<best['violations']*distance:
            best=dict(distance=distance,violations=violations,rows=[r+1 for r in rows])
        checked+=1
    result=dict(height=h,checked=checked,best=best,
                ratio=best['violations']/(h*best['distance']),
                by_distance=list(records.values()),seconds=time.monotonic()-started)
    print(json.dumps(result),flush=True)
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('heights',nargs='+',type=int)
    args=parser.parse_args()
    data=[run(h) for h in args.heights]
    Path(__file__).with_suffix('.json').write_text(json.dumps(data,indent=2)+'\n')
