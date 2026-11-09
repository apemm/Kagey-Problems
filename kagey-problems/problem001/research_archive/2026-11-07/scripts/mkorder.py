"""Write candidate orders. Usage: py mkorder.py h kind seed out"""
import sys, json, random
h=int(sys.argv[1]); kind=sys.argv[2]; rng=random.Random(int(sys.argv[3])); out=sys.argv[4]
odd=list(range(1,h+1,2)); ev=list(range(2,h+1,2))
E=[(a,b) for a in range(1,h+1) for b in range(a+1,h+1) if (b-a)%2]
if kind=='rand':
    o=E[:]; rng.shuffle(o)
elif kind=='starodd':
    rs=odd[:]; rng.shuffle(rs); o=[]
    for r in rs:
        es=ev[:]; rng.shuffle(es); o+=[tuple(sorted((r,e))) for e in es]
elif kind=='stareven':
    rs=ev[:]; rng.shuffle(rs); o=[]
    for r in rs:
        es=odd[:]; rng.shuffle(es); o+=[tuple(sorted((r,e))) for e in es]
json.dump(o,open(out,'w'))
