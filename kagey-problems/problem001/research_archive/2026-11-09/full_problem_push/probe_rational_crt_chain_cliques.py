"""Exploratory exact clique search for the split 4/3 CRT chain P graph."""
from math import isqrt
import json
import argparse


def square_divisors(n):
    """Divisors of n squared, factoring n rather than its square."""
    ds=[1];p=3
    while p*p<=n:
        if n%p:
            p+=2;continue
        exponent=0
        while n%p==0:
            n//=p;exponent+=1
        powers=[p**j for j in range(1,2*exponent+1)]
        ds += [d*v for d in list(ds) for v in powers]
        p+=2
    if n>1:
        ds += [d*v for d in list(ds) for v in (n,n*n)]
    return ds


def distances(t,step=98):
    ans=set()
    for odd in square_divisors(t):
        for power in (1,3):
            A=odd*(2**power);B=16*t*t//A
            if A*B!=16*t*t:continue
            num=B-A-6*t
            if num%50:continue
            k=num//50
            if k and k%step==0 and (A+B)%10==0:
                L=(A+B)//10
                assert 25*k*k+6*t*k+t*t==L*L
                ans.add(abs(k)//step)
    return sorted(ans)


def largest_clique(ds, target=5):
    D=set(ds); n=len(ds)
    neighbors=[sum(1<<j for j,y in enumerate(ds) if j!=i and abs(x-y) in D)
               for i,x in enumerate(ds)]
    best=[]
    def visit(chosen,candidates):
        nonlocal best
        if len(chosen)+candidates.bit_count()<=len(best):return
        if not candidates:
            if len(chosen)>len(best):best=chosen
            return
        while candidates:
            if len(chosen)+candidates.bit_count()<=len(best):return
            v=(candidates&-candidates).bit_length()-1
            candidates &= ~(1<<v)
            visit(chosen+[v],candidates&neighbors[v])
    visit([], (1<<n)-1)
    return [0]+[ds[v] for v in best]


def certificate(t, vertices, step=98):
    original_t=t
    t*=98//step
    points=[294*x for x in vertices]
    geometries=[]
    rows=points+[a+t for a in points]
    for i,a in enumerate(points):
        for j,b in enumerate(points[:i]):
            dx=4*(a-b)//3
            found=False
            for source,target in ((a,b),(b,a)):
                dy=target+t-source
                L=isqrt(dx*dx+dy*dy)
                if L*L==dx*dx+dy*dy:
                    lo=(source+target+t-L)//2; hi=(source+target+t+L)//2
                    assert (source+target+t-L)%2==0
                    rows += [lo,hi]
                    geometries.append(dict(source=source,target=target,L=L,low=lo,high=hi))
                    found=True;break
            assert found
    shift=1-min(rows)
    if shift%2==0:shift+=1
    return dict(t=t,normalized_t=original_t,step=step,indices=vertices,shift=shift,height=max(rows)+shift,
                labels=[[a+shift,a+t+shift] for a in points],
                relative_columns=[392*x for x in vertices],edges=geometries)


if __name__=="__main__":
    ap=argparse.ArgumentParser();ap.add_argument("--limit",type=int,default=100001)
    ap.add_argument("--step",type=int,choices=(2,98),default=98)
    ap.add_argument("--output",required=True);args=ap.parse_args()
    best=1;records=[]
    for t in range(1,args.limit+1,2):
        ds=distances(t,args.step)
        if len(ds)+1<=best:continue
        clique=largest_clique(ds)
        if len(clique)>best:
            best=len(clique);rec=certificate(t,clique,args.step);rec["clique_size"]=best
            records.append(rec);print(json.dumps(rec),flush=True)
    with open(args.output,"w",encoding="utf-8") as f:
        json.dump(dict(limit=args.limit,step=args.step,record_cliques=records),f,indent=2);f.write("\n")

