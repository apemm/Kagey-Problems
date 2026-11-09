"""Random 1,x,h boards (no pads): distances (in gaps) of the two middle cells of every binary clause,
with the clause sign pattern and the violation kind."""
import sys, random
from cegar_board import check
from v1laws import board
h=int(sys.argv[1]); T=int(sys.argv[2]); rng=random.Random(7); tally={}
for _ in range(T):
    cols=board(h,rng); B=[frozenset(c) for c in cols]; n,det=check(h,cols)
    for v,cs,Pw,partner in det:
        cells=set(cs)
        if partner: cells|=set(partner)
        if v=='rival':
            P=sorted(Pw)
            if len(P)==1:
                (px,pr),=P; ss=[t for t in B[px] if t!=pr and (t-pr)%2]; cells.add((px,ss[0]))
            else:
                (px,pr),(pz,ps)=P
                if pr==ps: t=min(B[px]&B[pz]); cells|={(px,t),(pz,t)}
                elif px!=pz: cells|={(px,ps),(pz,pr)}
        m=sorted({x for x,r in cells if x%4==2 and r in (1,h)})
        if len(m)==2:
            vals=tuple(next(iter(cols[x])) for x in m)
            key=(v,len(Pw),(m[1]-m[0])//4,'eq' if vals[0]==vals[1] else 'ne')
            tally[key]=tally.get(key,0)+1
for k in sorted(tally): print(k,tally[k])
