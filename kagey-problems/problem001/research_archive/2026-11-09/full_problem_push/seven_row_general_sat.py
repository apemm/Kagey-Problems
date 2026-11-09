"""Exact bounded seven-row SAT from the four/six-point collision hypergraph.

This covers all row partitions and column structures. Two proved near-bound
consequences are added when applicable: column-size bounds, and uniqueness
of a triple column at excess ten.
"""
from itertools import combinations
from pathlib import Path
import json
import multiprocessing as mp
import sys
import time
import traceback

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'.runtime'))
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles,collision


def bits(x):
    out=[]
    while x:
        b=x&-x
        out.append(b.bit_length()-1)
        x-=b
    return out


def owner_encoding(w,target,limit):
    """Exact row-pair ownership and compact tilted-axis constraints."""
    from pysat.card import CardEnc,EncType
    n=7*w
    pairs=list(combinations(range(7),2))
    pair_index={p:i for i,p in enumerate(pairs)}
    fv=lambda a,b:n+pair_index[min(a,b),max(a,b)]+1
    ev=lambda a,b,c:n+21+pair_index[min(a,b),max(a,b)]*w+c+1
    top=n+21+21*w
    clauses=[]
    for a,b in pairs:
        owners=[ev(a,b,c) for c in range(w)]
        clauses.append([-fv(a,b)]+owners)
        clauses.extend([-e,fv(a,b)] for e in owners)
        clauses.extend([-e,-f] for e,f in combinations(owners,2))
        for c,e in enumerate(owners):
            x,y=a*w+c+1,b*w+c+1
            clauses.extend(([-e,x],[-e,y],[-x,-y,e]))
    for a,b,c in combinations(range(7),3):
        for column in range(w):
            clauses.append([-ev(a,b,column),-fv(a,c),-fv(b,c),ev(a,c,column)])
    for c in range(w):
        clauses.extend([-r*w-c-1 for r in rows]
                       for rows in combinations(range(7),limit+1))
    if target-w==10:
        triple=[top+c+1 for c in range(w)]
        top+=w
        for c in range(w):
            clauses.extend([-r*w-c-1 for r in rows]+[triple[c]]
                           for rows in combinations(range(7),3))
        clauses.extend([-a,-b] for a,b in combinations(triple,2))
    cardinality=CardEnc.equals(list(range(1,n+1)),bound=target,top_id=top,encoding=EncType.totalizer)
    clauses+=cardinality.clauses
    top=cardinality.nv
    rects=rectangles(7,w)
    def tilted(R):
        ps=bits(R)
        return not(len({p%w for p in ps})==2 and len({p//w for p in ps})==2)
    tilts=[R for R in rects if tilted(R)]
    groups={k:set() for k in range(2,7)}
    def add(points,guard=None):
        sizes={}
        for p in bits(points):sizes[p%w]=sizes.get(p%w,0)+1
        if max(sizes.values())>limit:return
        if target-w==10 and sum(s>=3 for s in sizes.values())>1:return
        support=points if guard is None else points|(1<<(guard-1))
        groups[support.bit_count()].add(support)
    for R in tilts:
        add(R)
        corners=bits(R)
        for p in corners:
            c,r=p%w,p//w
            for s in range(7):
                if r!=s:add((R^(1<<p))|(1<<(s*w+c)),fv(r,s))
        for p,q in combinations(corners,2):
            c,r=p%w,p//w
            d,s=q%w,q//w
            remaining=R^(1<<p)^(1<<q)
            if c==d:add(remaining,fv(r,s))
            elif r==s:
                for row in range(7):add(remaining|(1<<(row*w+c))|(1<<(row*w+d)))
            else:add(remaining|(1<<(s*w+c))|(1<<(r*w+d)))
    at_point=[[] for _ in range(n)]
    for i,R in enumerate(tilts):
        for p in bits(R):at_point[p].append(i)
    for incident in at_point:
        for i,j in combinations(incident,2):add(tilts[i]^tilts[j])
    raw={k:len(v) for k,v in groups.items()}
    minimal={k:set() for k in groups}
    for k in range(2,7):
        for D in groups[k]:
            bs=[1<<p for p in bits(D)]
            if not any(sum(sub) in minimal[j] for j in range(2,k)
                       if minimal[j] for sub in combinations(bs,j)):
                minimal[k].add(D)
    clauses.extend([-p-1 for p in bits(D)] for family in minimal.values() for D in sorted(family))
    return clauses,rects,{'rectangles':len(rects),'variables':top,'clauses':len(clauses),
                        'pair_owner_variables':21*w,'pair_presence_variables':21,
                        'geometry_raw_by_size':raw,
                        'geometry_minimal_by_size':{k:len(v) for k,v in minimal.items()},
                        'owner_encoding':True}


def worker(send,w,target,solver_name,owners=False):
    try:
        from pysat.solvers import Solver
        from pysat.card import CardEnc,EncType
        import pysat
        began=time.monotonic()
        n=7*w
        rects=rectangles(7,w)
        excess=target-w
        limit=7
        for k in range(2,8):
            if 6+(7-k)**2//4<excess:
                limit=k-1
                break
        if owners:
            clauses,rects,info=owner_encoding(w,target,limit)
            info.update(proved_column_size_bound=limit,
                        proved_at_most_one_triple=excess==10,
                        encoding_seconds=time.monotonic()-began)
            send.send({'event':'encoded',**info})
            with Solver(name=solver_name,bootstrap_with=clauses) as solver:
                sat=solver.solve()
                result={'event':'result','status':'SAT' if sat else 'UNSAT',
                        'solver':solver_name,'pysat_version':pysat.__version__,
                        'info':info,'total_seconds':time.monotonic()-began,
                        'solver_stats':solver.accum_stats()}
                if sat:
                    model=set(solver.get_model())
                    black=sum(1<<p for p in range(n) if p+1 in model)
                    assert black.bit_count()==target and collision(rects,black) is None
                    points=sorted((p%w+1,p//w+1) for p in bits(black))
                    result['witness_one_based']=points
                    result['column_word']=','.join(''.join(str(r) for c,r in points if c==x)
                                                   for x in range(1,w+1))
                send.send(result)
            return
        clauses=[]
        for c in range(w):
            clauses.extend([-r*w-c-1 for r in rows]
                           for rows in combinations(range(7),limit+1))
        top=n
        if excess==10:
            triple=[n+c+1 for c in range(w)]
            top=n+w
            for c in range(w):
                clauses.extend([-r*w-c-1 for r in rows]+[triple[c]]
                               for rows in combinations(range(7),3))
            clauses.extend([-a,-b] for a,b in combinations(triple,2))
        count=CardEnc.equals(list(range(1,n+1)),bound=target,top_id=top,encoding=EncType.totalizer)
        clauses+=count.clauses
        top=count.nv
        def feasible(D):
            sizes={}
            for p in bits(D):sizes[p%w]=sizes.get(p%w,0)+1
            return max(sizes.values())<=limit and not(excess==10 and sum(s>=3 for s in sizes.values())>1)
        four={R for R in rects if feasible(R)}
        six=set()
        incident=[[] for _ in range(n)]
        for i,R in enumerate(rects):
            for p in bits(R):incident[p].append(i)
        for at in incident:
            for i,j in combinations(at,2):
                D=rects[i]^rects[j]
                group=four if D.bit_count()==4 else six
                if D not in group and feasible(D):group.add(D)
        minimal=[]
        for D in six:
            bs=[1<<p for p in bits(D)]
            if not any(D-a-b in four for a,b in combinations(bs,2)):minimal.append(D)
        clauses.extend([-p-1 for p in bits(D)] for D in sorted(four)+sorted(minimal))
        info={'rectangles':len(rects),'variables':top,'clauses':len(clauses),
              'geometry_four':len(four),'geometry_six':len(minimal),
              'proved_column_size_bound':limit,'proved_at_most_one_triple':excess==10,
              'encoding_seconds':time.monotonic()-began}
        send.send({'event':'encoded',**info})
        with Solver(name=solver_name,bootstrap_with=clauses) as solver:
            sat=solver.solve()
            result={'event':'result','status':'SAT' if sat else 'UNSAT',
                    'solver':solver_name,'pysat_version':pysat.__version__,
                    'info':info,'total_seconds':time.monotonic()-began,
                    'solver_stats':solver.accum_stats()}
            if sat:
                model=set(solver.get_model())
                black=sum(1<<p for p in range(n) if p+1 in model)
                assert black.bit_count()==target and collision(rects,black) is None
                points=sorted((p%w+1,p//w+1) for p in bits(black))
                result['witness_one_based']=points
                result['column_word']=','.join(''.join(str(r) for c,r in points if c==x)
                                               for x in range(1,w+1))
            send.send(result)
    except BaseException:
        send.send({'event':'error','status':'error','traceback':traceback.format_exc()})
    finally:send.close()


def main():
    w,target=int(sys.argv[1]),int(sys.argv[2])
    assert w>=4
    cap=float(sys.argv[3]) if len(sys.argv)>3 else 180
    solver=sys.argv[4] if len(sys.argv)>4 else 'cadical195'
    owners='owners' in sys.argv[5:]
    receive,send=mp.Pipe(duplex=False)
    child=mp.Process(target=worker,args=(send,w,target,solver,owners))
    begin=time.monotonic();child.start();send.close()
    result=None;encoded=None
    while child.is_alive() and time.monotonic()-begin<cap:
        try:
            if not receive.poll(min(1,max(0,cap-time.monotonic()+begin))):continue
            event=receive.recv()
        except (EOFError,OSError):break
        print(json.dumps(event),flush=True)
        if event['event']=='encoded':encoded=event
        else:result=event
    if child.is_alive():child.terminate()
    child.join(5)
    while True:
        try:
            if not receive.poll():break
            event=receive.recv()
        except (EOFError,OSError):break
        if event['event']!='encoded':result=event
    if result is None:result={'status':'unknown','reason':'wall-clock cap','encoded':encoded}
    output={'rows':7,'columns':w,'target':target,'scope':'all black sets',
            'cap_seconds':cap,'wall_seconds':time.monotonic()-begin,'owner_encoding':owners,**result}
    suffix='_owners' if owners else ''
    (HERE/f'general_h7_w{w}_b{target}_{solver}{suffix}.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output),flush=True)


if __name__=='__main__':
    mp.freeze_support();main()
