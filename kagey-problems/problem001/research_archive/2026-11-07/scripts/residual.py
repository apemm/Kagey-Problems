"""Random orders obeying the slot rule (Prop 18) on a plain "1, x, h" board; tally the violations that
depend on no middle cell (order-only), by kind, and separately those with 1 or 2 middle cells."""
import sys, random
from cegar_board import check
def v2(n):
    c=0
    while n%2==0: n//=2;c+=1
    return c
h=int(sys.argv[1]); T=int(sys.argv[2]); rng=random.Random(int(sys.argv[3]) if len(sys.argv)>3 else 3)
E=[(a,b) for a in range(1,h+1) for b in range(a+1,h+1) if (b-a)%2]; q=len(E)
def tw(e):
    o=e[0] if e[0]%2 else e[1]
    if o in (1,h): return None
    if o%4==1: t=v2(o-1);w=((o-1)>>t)%4
    else: t=v2(h-o);w=(-((h-o)>>t))%4
    return t,w
def order():
    pools={0:[],1:[],2:[],3:[]}; rest=[]
    for e in E:
        ev=e[0] if e[0]%2==0 else e[1]; x=tw(e)
        if x and x[0]==2: pools[0 if x[1]==1 else 2].append(e)
        else: pools[1 if ev%4==0 else 3].append(e)
    for p in pools.values(): rng.shuffle(p)
    out=[None]*q
    for j in range(q):
        p=pools[j%4]
        if p: out[j]=p.pop()
    rest=[e for p in pools.values() for e in p]; rng.shuffle(rest)
    for j in range(q):
        if out[j] is None: out[j]=rest.pop()
    return out
def kind(c):
    return 'D' if c[0]%4==0 else ('M' if c[0]%4==2 else 'F')
tally={}; nb=0
for _ in range(T):
    od=order(); cols=[]
    for j,e in enumerate(od):
        cols.append(set(e))
        if j<q-1: cols+=[{1},{rng.choice([1,h])},{h}]
    B=[frozenset(c) for c in cols]; n,det=check(h,cols); nb+=1
    # ignore the first and last W columns (end effects)
    W=1+(h-1)**2//4
    for v,cs,Pw,partner in det:
        if min(x for x,_ in cs)<W or max(x for x,_ in cs)>len(cols)-W: continue
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
        nm=len({x for x,r in cells if x%4==2 and r in (1,h)})
        blk=''.join(sorted(kind(c) for c in cs if c not in set(Pw)))
        wh=''.join(sorted(kind(c) for c in Pw))
        key=(nm,v,len(Pw),blk,wh)
        tally[key]=tally.get(key,0)+1
print('h',h,'boards',nb,'q',q)
for k in sorted(tally,key=lambda k:(k[0],-tally[k])):
    print('%7.2f per board'%(tally[k]/nb),k)
