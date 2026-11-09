"""Test periodic-to-boundary single cuts as a possible sea reset mechanism."""
from itertools import product
from pathlib import Path
import json
import time
import sys
from isolated_lowering_probe import sea,HERE


def quotient(cells,period):
    out={}
    for x,r in cells:
        k=x%period
        if k in out and out[k]!=r:return None
        out[k]=r
    return tuple(sorted(out.items()))


def minimize(patterns):
    kept=[]
    for P in sorted(set(patterns),key=lambda P:(len(P),P)):
        s=set(P)
        if not any(set(Q)<=s for Q in kept):kept.append(P)
    return kept


def main():
    h=int(sys.argv[1]);maximum=int(sys.argv[2]);begin=time.monotonic()
    patterns,stats=sea.forbidden_patterns(h,time.monotonic()+120)
    records=[]
    for p in range(1,maximum+1):
        full=[];cut=[]
        for P in patterns:
            for shift in range(p):
                Q=quotient(((x+shift,r) for x,r in P),p)
                if Q is not None:full.append(Q)
            for shift in range(-P[-1][0],0):
                if any(x+shift>=0 and r!=1 for x,r in P):continue
                Q=quotient(((x+shift,r) for x,r in P if x+shift<0),p)
                if Q is not None:cut.append(Q)
        full=minimize(full);cut=minimize(cut)
        accepted=0;bad=[]
        for word in product(range(1,h+1),repeat=p):
            if any(all(word[i]==r for i,r in P) for P in full):continue
            accepted+=1
            allowed=[]
            for phase in range(p):
                if not any(all(word[(i+phase)%p]==r for i,r in P) for P in cut):allowed.append(phase)
            if not allowed:bad.append(word)
        record={'period':p,'accepted':accepted,'no_constant_cut':len(bad),
                'first_examples':bad[:8],'full_constraints':len(full),'cut_constraints':len(cut)}
        records.append(record);print(json.dumps(record),flush=True)
        if bad:break
    out={'height':h,'requested_maxperiod':maximum,'geometry':stats,'periods':records,
         'seconds':time.monotonic()-begin}
    (HERE/f'constant_cut_h{h}_p{maximum}.json').write_text(json.dumps(out,indent=2)+'\n')


if __name__=='__main__':main()
