# For each vertex (non-inert odd row) at slot a, level s=tau-2, list law-D partners a+2^s d' (fixed-cell case):
# class-fatal (e = w + d' mod 4)? far side? divisible? -> fatal / escaped-by-size / safe-by-residue
import json
h=11; D='../data/'
def v2(n):
    c=0
    while n%2==0: n//=2;c+=1
    return c
def info(e):
    o=e[0] if e[0]%2 else e[1]; ev=e[0]+e[1]-o
    if o in (1,h): return o,ev,None,None,None,None
    if o%4==1: t=v2(o-1);u=(o-1)>>t;w=u%4;sg=1
    else: t=v2(h-o);u=(h-o)>>t;w=(-u)%4;sg=h
    return o,ev,t,u,w,sg
for f in ('cegar_h11_mod4_j1_t4.json','cegar_h11_mod4_j2_t4.json'):
    od=json.load(open(D+f))['order']; q=len(od)
    print(f); tally={}
    for a,ea in enumerate(od):
        r,_,t,u,w,sg=info(ea)
        if t is None: continue
        s=t-2
        for b,eb in enumerate(od):
            if b==a or (b-a)%(2**s): continue
            d=(b-a)>>s
            if d%2==0: continue
            e=info(eb)[1]
            cls=(e%4==(w+d)%4)
            far=(e>r) if sg==1 else (e<r)
            div=(u*(e-r))%d==0
            key=('tight' if abs(d)==1 else 'long', 'resid-safe' if not cls else ('FATAL' if far and div else ('near' if not far else 'nodiv')))
            tally[key]=tally.get(key,0)+1
            if abs(d)==1 and cls: print('  slot',a,'row',r,'tau',t,'-> slot',b,'e',e,'escape:', 'near' if not far else ('nodiv' if not div else 'FATAL?'))
    print(tally)
# where are the class-fatal, far, divisible events? report sea column gap index
print('--- fatal-by-law events and the gap of their sea corner (TR=4: gaps 0-3 and 26-28 are free)')
for f in ('cegar_h11_mod4_j1_t4.json','cegar_h11_mod4_j2_t4.json'):
    od=json.load(open(D+f))['order']
    for a,ea in enumerate(od):
        r,_,t,u,w,sg=info(ea)
        if t is None: continue
        s=t-2
        for b,eb in enumerate(od):
            if b==a or (b-a)%(2**s): continue
            d=(b-a)>>s
            if d%2==0: continue
            e=info(eb)[1]
            if e%4==(w+d)%4 and ((e>r) if sg==1 else (e<r)) and (u*(e-r))%d==0:
                x0=4*a+(u*(e-r))//d if sg==1 else 4*a-(u*(e-r))//d
                print(f[-12:],'vertex slot',a,'row',r,'partner slot',b,'e',e,'sea col',x0,'gap',x0//4,'4th corner col',x0+4*(b-a))
