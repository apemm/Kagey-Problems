"""Dump geometry of order-only violations by class on slot-rule random boards (relative coords)."""
import sys, random
exec(open('residual.py').read().split("tally={}; nb=0")[0])
want=eval(sys.argv[4]); shown=0
for _ in range(T):
    od=order(); cols=[]
    for j,e in enumerate(od):
        cols.append(set(e))
        if j<q-1: cols+=[{1},{rng.choice([1,h])},{h}]
    B=[frozenset(c) for c in cols]; n,det=check(h,cols); W=1+(h-1)**2//4
    for v,cs,Pw,partner in det:
        if min(x for x,_ in cs)<W or max(x for x,_ in cs)>len(cols)-W: continue
        blk=''.join(sorted(kind(c) for c in cs if c not in set(Pw))); wh=''.join(sorted(kind(c) for c in Pw))
        if (v,len(Pw),blk,wh)!=want: continue
        x0=min(x for x,_ in cs)//4*4
        rel=lambda L:[(x-x0,r) for x,r in L]
        bl=[c for c in cs if c not in set(Pw)]
        print('blk',rel(bl),'white',rel(sorted(Pw)),'partner-blk',rel([c for c in (partner or []) if c not in set(Pw)]))
        shown+=1
        if shown>=6: sys.exit()
