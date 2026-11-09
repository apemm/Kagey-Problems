"""Law (C), general form: whites L, R in one row y, black B = fixed row-1 (or row-h) cell, black T a double
point, LR and BT diameters of one circle. Check p^2 + (t-1)^2 = n^2 and which white column is a double
column that must contain row 1 (resp. h)."""
import sys
exec(open('residual.py').read().split("tally={}; nb=0")[0])
from collections import Counter
ok=bad=0; trip=Counter()
for _ in range(T):
    od=order(); cols=[]
    for j,e in enumerate(od):
        cols.append(set(e))
        if j<q-1: cols+=[{1},{rng.choice([1,h])},{h}]
    n_,det=check(h,cols); W=1+(h-1)**2//4
    for v,cs,Pw,partner in det:
        if min(x for x,_ in cs)<W or max(x for x,_ in cs)>len(cols)-W or v!='rival' or len(Pw)!=2: continue
        blk=sorted(c for c in cs if c not in set(Pw)); wh=sorted(Pw)
        if ''.join(sorted(kind(c) for c in blk))!='DF' or ''.join(sorted(kind(c) for c in wh))!='DF': continue
        f=[c for c in blk if c[0]%4][0]; d=[c for c in blk if c[0]%4==0][0]
        (xl,y),(xr,y2)=wh
        p=abs(d[0]-f[0]); t=abs(d[1]-f[1]); nn=xr-xl
        g=y==y2 and xl+xr==f[0]+d[0] and 2*y==f[1]+d[1] and p*p+t*t==nn*nn
        dc=[x for x in (xl,xr) if x%4==0]
        g=g and len(dc)==1 and f[1] in cols[dc[0]]
        ok+=g; bad+=not g; trip[(min(p,t),max(p,t),nn)]+=1
print('law C general:',ok,'agree',bad,'fail; triples',sorted(trip.items()))
