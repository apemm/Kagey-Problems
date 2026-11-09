"""Test the mod-4 form of law (D) at fixed cells: vertex odd row r, tau = v2 on its active side,
r - 1 (or h - r) = 2^tau u, d = 2^(tau-2) d'. Predicted: fatal iff the partner's even row e satisfies
e = 1 + u d' (mod 4) on the row-1 side, e = 3 + u d' (mod 4) on the row-h side, e on the far side, and
d' | u (e - r). Compares predicted fixed-cell events with the checker's DDS events (vertex D, gap 2)."""
import sys, random
from cegar_board import check
from v1laws import board, v2
h=int(sys.argv[1]); T=int(sys.argv[2]); rng=random.Random(9)
agree=miss=extra=0
for _ in range(T):
    cols=board(h,rng); n,det=check(h,cols)
    seen=set()
    for v,cs,Pw,partner in det:
        if v!='rival' or len(Pw)!=1: continue
        blk=[c for c in cs if c not in set(Pw)]
        if sorted(c[0]%4==0 for c in blk)!=[False,True,True]: continue
        (X,)=Pw
        V=max(blk,key=lambda c:(c[0]-X[0])**2+(c[1]-X[1])**2)
        s=[c for c in blk if c[0]%4][0]
        if s[0]%4==2: continue
        q=[c for c in blk if c!=V and c[0]%4==0][0]
        seen.add((V,q))
    pred=set()
    D=[x for x in range(0,len(cols),4)]
    for x in D:
        for r in cols[x]:
            if r%2==0 or r in (1,h): continue
            side=1 if r%4==1 else h
            tau=v2(r-1) if side==1 else v2(h-r); u=((r-1) if side==1 else (h-r))>>tau
            if tau<2: continue
            for y in D:
                if y==x: continue
                d=(y-x)//4
                if v2(d)!=tau-2: continue
                dp=d>>(tau-2) if d>0 else -((-d)>>(tau-2))
                for e in cols[y]:
                    if e%2: continue
                    if side==1 and not e>r: continue
                    if side==h and not e<r: continue
                    if (u*(e-r))%dp: continue
                    if e%4 != ((1 if side==1 else 3)+u*dp)%4: continue
                    # the sea corner and the completion must lie on the board
                    x0 = x + ((r-1)*(e-r))//(4*d) if side==1 else x - ((h-r)*(e-r))//(4*d)
                    if not (0<=x0<len(cols) and 0<=x0+4*d<len(cols)): continue
                    pred.add(((x,r),(y,e)))
    [print("extra",p,len(cols)) for p in pred-seen]
    agree+=len(pred&seen); miss+=len(seen-pred); extra+=len(pred-seen)
print(h,"agree",agree,"checker-only",miss,"predicted-only",extra)
