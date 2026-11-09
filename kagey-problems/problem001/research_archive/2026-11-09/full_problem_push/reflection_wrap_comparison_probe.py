"""Exact finite check of interval versus cyclic reflection violations."""
from itertools import combinations
from pathlib import Path
import json
out=[]
for h in range(8,21,2):
    n=h//2
    best=0
    ex=None
    for comb in combinations(range(h),n):
        aset=set(comb)
        vi=sum(1 for a in aset for b in aset if 0<=2*a-b<h and 2*a-b not in aset)
        vc=sum(1 for a in aset for b in aset if (2*a-b)%h not in aset)
        if vi==0:
            assert vc==0,(h,comb,vc)
            continue
        if vc/vi>best:
            best=vc/vi
            ex=(comb,vi,vc)
    row={"height":h,"max_cyclic_over_interval":best,"example":[i+1 for i in ex[0]],"interval":ex[1],"cyclic":ex[2]}
    print(json.dumps(row),flush=True)
    out.append(row)
Path(__file__).with_suffix(".json").write_text(json.dumps({"scope":"finite evidence only","results":out},indent=2)+"\n")

