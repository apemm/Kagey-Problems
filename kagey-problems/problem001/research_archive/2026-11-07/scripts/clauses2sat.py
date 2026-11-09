"""For a fixed found board, resample the interior middle cells at random and collect the forbidden
combinations of middle cells (the 2-SAT clauses). Report units, binaries and their sign pattern."""
import json, random, sys
from cegar_board import check
f=sys.argv[1]; N=int(sys.argv[2])
d=json.load(open(f)); h=d['h']; W=d['W']; TR=d['TR']; cols0=[set(c) for c in d['cols']]; q=len(d['order'])
mids=[W+4*j+2 for j in range(TR, q-1-TR)]
rng=random.Random(1); CL={}
for _ in range(N):
    cols=[set(c) for c in cols0]
    for x in mids: cols[x]={rng.choice([1,h])}
    B=[frozenset(c) for c in cols]; n,det=check(h,cols)
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
        lits=tuple(sorted({(x,next(iter(cols[x]))) for x,r in cells if x in set(mids)}))
        CL[lits]=CL.get(lits,0)+1
gap=lambda x:(x-W)//4
units=[c for c in CL if len(c)==1]; bins=[c for c in CL if len(c)==2]; zero=[c for c in CL if len(c)==0]
print('order-only violations (no middle cell):',len(zero),' units:',len(units),' binaries:',len(bins))
print('units (gap: forbidden value):',sorted((gap(c[0][0]),c[0][1]) for c in units))
for c in sorted(bins):
    (x1,v1),(x2,v2)=c
    print('  forbid gap%d=%d & gap%d=%d'%(gap(x1),v1,gap(x2),v2), 'dist',gap(x2)-gap(x1))
print('found x:',[next(iter(cols0[x])) for x in mids])
