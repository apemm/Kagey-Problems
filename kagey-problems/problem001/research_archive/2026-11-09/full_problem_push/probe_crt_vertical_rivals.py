"""Enumerate in-strip vertical rivals for rational-slope CRT labels.

A label is (a odd, b even), with t=b-a. The nearby-label rule is
dx = numerator*k, da=db=denominator*k. All centers are multiples of
slot_step. This enumerates Pythagorean diagonals, not the CRT board.
"""
from pathlib import Path
from math import gcd,isqrt
import argparse,json,time

def probe(h,num,den,slot_step):
    assert gcd(num,den)==1 and num>0 and den>0
    by_t={}
    distances={}
    geometries=0
    for m in range(2,isqrt(h-1)+1):
        for n in range(1,m):
            if (m-n)%2==0 or gcd(m,n)!=1: continue
            hyp=m*m+n*n
            if hyp>=h: continue
            even=2*m*n
            odd=m*m-n*n
            for g in range(1,(h-1)//hyp+1,2):
                dx=g*even
                if dx%slot_step or dx%num: continue
                da=dx*den//num
                if da%2 or da>=h: continue
                length=g*hyp
                for dy in (g*odd,-g*odd):
                    t=dy-da
                    assert t%2
                    if abs(t)>=h: continue
                    rows=(0,t,da,dy,(dy-length)//2,(dy+length)//2)
                    lower=1-min(rows)
                    upper=h-max(rows)
                    lower += (1-lower)%2
                    upper -= (upper-1)%2
                    if lower>upper: continue
                    geometries+=1
                    by_t.setdefault(t,[]).extend(((lower,upper),(lower+da,upper+da)))
                    distances.setdefault(t,set()).add(da)
    unsafe=0
    nonzero7_unsafe=0
    for t, intervals in by_t.items():
        intervals.sort()
        left,right=intervals[0]
        subtotal=0
        for a,b in intervals[1:]:
            if a<=right+2: right=max(right,b)
            else:
                subtotal+=(right-left)//2+1
                left,right=a,b
        subtotal+=(right-left)//2+1
        unsafe+=subtotal
        if t%7: nonzero7_unsafe+=subtotal
    all_labels=(h//2)*((h+1)//2)
    nonzero7_total=0
    for a in range(1,h+1,2):
        total=h//2
        # Even b congruent to a modulo 7, period 14.
        first=a%7
        if first%2: first+=7
        if first==0: first=14
        equal=0 if first>h else (h-first)//14+1
        nonzero7_total += total-equal
    largest=sorted(((len(v),t,sorted(v)) for t,v in distances.items()),
                   reverse=True)[:12]
    triangles=[]
    for t, ds in distances.items():
        ordered=sorted(ds)
        example=next(((a,b,a+b) for a in ordered for b in ordered
                      if a<=b and a+b in ds),None)
        if example: triangles.append((t,example))
    return dict(height=h,slope=[num,den],slot_step=slot_step,
                normalized_geometries=geometries,unsafe_t_count=len(by_t),
                largest_distance_sets=largest,
                distance_set_additive_triples=triangles[:12],
                t_with_additive_triples=len(triangles),
                unsafe_labels=unsafe,total_labels=all_labels,
                unsafe_fraction=unsafe/all_labels,
                nonzero7_unsafe_labels=nonzero7_unsafe,
                nonzero7_total_labels=nonzero7_total,
                nonzero7_unsafe_fraction=nonzero7_unsafe/nonzero7_total)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--heights",default="256,512,1024,2048,4096,8192,16384")
    ap.add_argument("--num",type=int,default=4)
    ap.add_argument("--den",type=int,default=3)
    ap.add_argument("--slot-step",type=int,default=98)
    ap.add_argument("--output",default="continuation_crt_vertical_probe.json")
    args=ap.parse_args()
    result=[]
    for h in map(int,args.heights.split(",")):
        start=time.monotonic()
        row=probe(h,args.num,args.den,args.slot_step)
        row["seconds"]=time.monotonic()-start
        result.append(row)
        print(json.dumps(row),flush=True)
    Path(__file__).with_name(args.output).write_text(json.dumps(result,indent=2)+"\n")

if __name__=="__main__": main()

