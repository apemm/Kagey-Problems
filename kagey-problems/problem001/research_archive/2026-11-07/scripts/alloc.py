"""Counting check of the protection allocation (Prop 19 residues at even slots, windows at odd slots).
Slots 1..q (v2 classes); edges classified by tau, w, inverted. Inverted tau>=4 edges must take residue
slots: w=3 at v2 = tau-1, w=1 at v2 >= tau. Hot: w=3 at v2=1, w=1 at v2>=2, or odd slots."""
import sys
def v2(n):
    c=0
    while n%2==0: n//=2;c+=1
    return c
for h in map(int, sys.argv[1:]):
    k=(h-1)//2; q=k*(k+1)
    E=[(o,e) for o in range(1,h+1,2) for e in range(2,h,2)]
    slots={}
    for j in range(1,q+1): slots[v2(j)]=slots.get(v2(j),0)+1
    need={}  # residue-forced demands: key (kind, level spec)
    inv4=[];hot={1:0,3:0};other=0
    for o,e in E:
        if o in (1,h): other+=1; continue
        if o%4==1: t=v2(o-1);u=(o-1)>>t;w=u%4;inv=e>o
        else: t=v2(h-o);u=(h-o)>>t;w=(-u)%4;inv=e<o
        if t==2: hot[w]+=1
        elif t>=4 and inv: inv4.append((t,w))
        else: other+=1
    # residue slots for inverted tau>=4: w=3 exactly v2=t-1, w=1 v2>=t
    free=dict(slots); ok=True
    for t,w in sorted(inv4,key=lambda x:(x[1]!=3,-x[0])):
        if w==3:
            if free.get(t-1,0)>0: free[t-1]-=1
            else: ok=False
        else:
            c=[s for s in sorted(free) if s>=t and free[s]>0]
            if c: free[c[0]]-=1
            else: ok=False
    even=sum(v for s,v in free.items() if s>=1); odd=free[0]
    # hot w=3 into v2=1 first, hot w=1 into v2>=2; overflow to odd slots
    h3=min(hot[3],free.get(1,0)); h1=min(hot[1],sum(v for s,v in free.items() if s>=2))
    overflow=hot[3]-h3+hot[1]-h1
    spare_even=even-h3-h1
    print('h',h,'q',q,'inv tau>=4',len(inv4),'placed',ok,'hot w1/w3',hot[1],hot[3],
          'odd slots',odd,'odd demand',other+overflow-spare_even if spare_even<0 else other+overflow,
          'spare even',spare_even)
