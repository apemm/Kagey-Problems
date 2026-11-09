"""For each violation of a random 1,x,h board, count the middle cells (columns = 2 mod 4) whose value
the violation depends on: corners of the rectangle, of its tilted partner, and of its axis rival."""
import sys, random
from cegar_board import check
from v1laws import board
h=int(sys.argv[1]); T=int(sys.argv[2]); rng=random.Random(5)
tally={}
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
                if pr==ps:
                    t=min(B[px]&B[pz]); cells|={(px,t),(pz,t)}
                elif px!=pz:
                    cells|={(px,ps),(pz,pr)}
        mids={x for x,r in cells if x%4==2 and r in (1,h)}
        tally[len(mids)]=tally.get(len(mids),0)+1
print(h, sorted(tally.items()))
