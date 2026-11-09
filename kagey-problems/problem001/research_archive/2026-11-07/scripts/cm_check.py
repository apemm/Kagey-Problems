"""Check law (C_m) and law (P) against the order-only DF/DF rivals and DD/MM rivals on slot-rule boards."""
import sys
exec(open('residual.py').read().split("tally={}; nb=0")[0])
import math
okC=badC=okP=badP=0
for _ in range(T):
    od=order(); cols=[]
    for j,e in enumerate(od):
        cols.append(set(e))
        if j<q-1: cols+=[{1},{rng.choice([1,h])},{h}]
    B=[frozenset(c) for c in cols]; n,det=check(h,cols); W=1+(h-1)**2//4
    for v,cs,Pw,partner in det:
        if min(x for x,_ in cs)<W or max(x for x,_ in cs)>len(cols)-W or v!='rival' or len(Pw)!=2: continue
        blk=sorted(c for c in cs if c not in set(Pw)); wh=sorted(Pw)
        ks=''.join(sorted(kind(c) for c in blk)); kw=''.join(sorted(kind(c) for c in wh))
        if (ks,kw)==('DF','DF'):
            d=[c for c in blk if c[0]%4==0][0]; f=[c for c in blk if c[0]%4][0]
            D=abs(d[0]-f[0]-(1 if f[1]==1 else -1))//4
            m=round(math.sqrt(D)); r=d[1]
            ok = m*m==D and ((f[1]==1 and r==1+4*m) or (f[1]==h and r==h-4*m))
            okC+=ok; badC+=not ok
            if not ok: print('C?',blk,wh)
        if (ks,kw)==('DD','MM') and wh[0][0]==wh[1][0] and wh[0][1] not in (1,h) and wh[1][1] not in (1,h):
            (x1,a),(x2,b)=blk; D=abs(x2-x1)//4; L=wh[1][1]-wh[0][1]
            ok = D%2==1 and 16*D*D+(b-a)**2==L*L and (a-b)%2==1
            okP+=ok; badP+=not ok
print('C_m law', okC, 'agree', badC, 'fail;  P law', okP, 'agree', badP, 'fail')
