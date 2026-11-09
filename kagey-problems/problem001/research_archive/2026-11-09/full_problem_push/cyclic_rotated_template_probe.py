"""Small exact algebra probe for cyclic rotated full-box templates."""
import itertools, json, time, math
from pathlib import Path

def protected(n):
    out=set()
    for k in range(2):
        for a in range(2):
            if not k and not a: continue
            for b in range(2):
                out.add(tuple((k*i*(i-1)//2+a*i+b)%2 for i in range(n)))
    return out

def run(n,a=1,b=2):
    t0=time.time()
    cs=[]
    for inds in itertools.combinations(range(n),n//2):
        c=[0]*n
        for j in inds:c[j]=1
        cs.append(tuple(c))
    ts=list(itertools.product(range(2),repeat=n))
    surv=0; hist={}; unusual=[]
    prot=protected(n)
    for c in cs:
        cys=[[[c[(offset+b*i+a*j)%n] for j in range(n)] for i in range(n)] for offset in range(math.gcd(a*a+b*b,n))]
        for t in ts:
            valid=True
            for cy in cys:
                masks=[sum((cy[i][j]==t[(a*i-b*j)%n])<<j for j in range(n)) for i in range(n)]
                labels=set(masks)
                if any(x&y for x in labels for y in labels if x!=y):
                    valid=False
                    break
            if not valid:continue
            surv+=1
            num=len(labels-{0})
            hist[num]=hist.get(num,0)+1
            if (c not in prot or num>2) and len(unusual)<20:
                unusual.append({"c":c,"t":t,"blocks":num,"masks":masks})
    return {"n":n,"direction":[a,b],"survivors":surv,"component_histogram":hist,"unusual":unusual,"seconds":time.time()-t0}

if __name__=="__main__":
    result=[run(n) for n in (4,6,8,10,12)]
    p=Path(__file__).with_suffix(".json")
    p.write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))

