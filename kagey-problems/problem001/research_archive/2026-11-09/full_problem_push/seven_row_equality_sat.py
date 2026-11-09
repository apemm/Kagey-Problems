"""Bounded exact SAT for a fixed balanced seven-row equality partition.

Each edge of K_3,4 occurs in one double column. Every other column is a
singleton. Geometry uses the exact four/six-point hypergraph, with no hidden
flags. UNSAT refers only to the specified partition and width.
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
from verify_narrow import rectangles,axis_rectangles,collision


def bits(x):
    out=[]
    while x:
        b=x&-x
        out.append(b.bit_length()-1)
        x-=b
    return out


def feasible(support,w,edges):
    columns={}
    for pos in bits(support):
        c,r=pos%w,pos//w
        columns[c]=columns.get(c,0)|(1<<r)
    used=set()
    for mask in columns.values():
        if mask.bit_count()>2:return False
        if mask.bit_count()==2:
            if mask not in edges or mask in used:return False
            used.add(mask)
    return True


def compact_supports(rects,tilted,w,part,edge_set,feasible_test=None):
    groups={k:set() for k in range(2,7)}
    def add(D):
        allowed=feasible_test(D) if feasible_test is not None else feasible(D,w,edge_set)
        if allowed:groups[D.bit_count()].add(D)
    tilt_rects=[R for R,t in zip(rects,tilted) if t]
    for R in tilt_rects:
        add(R)
        corners=bits(R)
        for p in corners:
            c,r=p%w,p//w
            for s in range(7):
                if ((1<<r)|(1<<s)) in edge_set:add((R^(1<<p))|(1<<(s*w+c)))
        for p,q in combinations(corners,2):
            c,r=p%w,p//w
            d,s=q%w,q//w
            remaining=R^(1<<p)^(1<<q)
            if c==d:
                if ((1<<r)|(1<<s)) in edge_set:add(remaining)
            elif r==s:
                for row in range(7):add(remaining|(1<<(row*w+c))|(1<<(row*w+d)))
            else:
                add(remaining|(1<<(s*w+c))|(1<<(r*w+d)))
    incident=[[] for _ in range(7*w)]
    for i,R in enumerate(tilt_rects):
        for p in bits(R):incident[p].append(i)
    for at in incident:
        for i,j in combinations(at,2):add(tilt_rects[i]^tilt_rects[j])
    raw={k:len(v) for k,v in groups.items()}
    minimal={k:set() for k in groups}
    for k in range(2,7):
        for D in groups[k]:
            bs=[1<<p for p in bits(D)]
            if not any(sum(sub) in minimal[j] for j in range(2,k)
                       if minimal[j] for sub in combinations(bs,j)):
                minimal[k].add(D)
    return [D for k in range(2,7) for D in sorted(minimal[k])],{
        'geometry_raw_by_size':raw,
        'geometry_minimal_by_size':{k:len(v) for k,v in minimal.items()}}


def encode(w,part,compact=False):
    other=[r for r in range(7) if r not in part]
    edges=sorted((1<<a)|(1<<b) for a in part for b in other)
    edge_set=set(edges)
    types=[1<<r for r in range(7)]+edges
    n=7*w
    tv=lambda c,j:n+19*c+j+1
    clauses=[]
    for c in range(w):
        clauses.append([tv(c,j) for j in range(19)])
        clauses.extend([-tv(c,i),-tv(c,j)] for i,j in combinations(range(19),2))
        for r in range(7):
            holders=[tv(c,j) for j,mask in enumerate(types) if mask>>r&1]
            point=r*w+c+1
            clauses.extend([-v,point] for v in holders)
            clauses.append([-point]+holders)
    for j in range(7,19):
        clauses.append([tv(c,j) for c in range(w)])
        clauses.extend([-tv(c,j),-tv(d,j)] for c,d in combinations(range(w),2))
    # One fixed double lies in the first half after horizontal reflection.
    clauses.append([tv(c,7) for c in range((w+1)//2)])
    rects=rectangles(7,w)
    axis=set(axis_rectangles(7,w))
    tilted=[R not in axis for R in rects]
    if compact:
        supports,geometry=compact_supports(rects,tilted,w,part,edge_set)
        clauses.extend([-p-1 for p in bits(D)] for D in supports)
        info={'rectangles':len(rects),'tilted_rectangles':sum(tilted),
              'variables':n+19*w,'clauses':len(clauses),
              'compact_axis_rivals':True,**geometry}
        return clauses,rects,info
    support4={R for R,t in zip(rects,tilted) if t and feasible(R,w,edge_set)}
    support6=set()
    at_point=[[] for _ in range(n)]
    for index,R in enumerate(rects):
        for p in bits(R):at_point[p].append(index)
    for incident in at_point:
        for i,j in combinations(incident,2):
            if not(tilted[i] or tilted[j]):continue
            D=rects[i]^rects[j]
            family=support4 if D.bit_count()==4 else support6
            if D not in family and feasible(D,w,edge_set):family.add(D)
    minimal6=[]
    for D in support6:
        cell_bits=[1<<p for p in bits(D)]
        if not any(D-a-b in support4 for a,b in combinations(cell_bits,2)):
            minimal6.append(D)
    for D in sorted(support4)+sorted(minimal6):
        clauses.append([-p-1 for p in bits(D)])
    info={'rectangles':len(rects),'tilted_rectangles':sum(tilted),
          'geometry_four_clauses':len(support4),
          'geometry_six_clauses':len(minimal6),
          'variables':n+19*w,'clauses':len(clauses)}
    return clauses,rects,info


def worker(pipe,w,part,solver_name,repair=None,compact=False):
    try:
        from pysat.solvers import Solver
        import pysat
        began=time.monotonic()
        clauses,rects,info=encode(w,part,compact=compact)
        phases=None
        if repair is not None:
            removed,free_count=repair
            records=json.loads((HERE/'seven_row_twenty_repair_candidates.json').read_text())
            record=next(r for r in records if r['removed_column']==removed)
            word=[sum(1<<(int(r)-1) for r in c) for c in record['column_word'].split(',')]
            assert w==20 and part==(1,3,5)
            other=[r for r in range(7) if r not in part]
            edges=sorted((1<<a)|(1<<b) for a in part for b in other)
            types=[1<<r for r in range(7)]+edges
            doubles=[c for c,b in enumerate(word) if b.bit_count()==2]
            free=set(sorted(doubles,key=lambda c:abs(c-(removed-1)))[:free_count])
            for c in doubles:
                if c not in free:
                    clauses.append([7*w+19*c+types.index(word[c])+1])
            phases=[]
            for c,b in enumerate(word):
                phases.extend((r*w+c+1)*(1 if b>>r&1 else -1) for r in range(7))
                phases.extend((7*w+19*c+j+1)*(1 if mask==b else -1)
                              for j,mask in enumerate(types))
            info['pinned_double_columns']=[c+1 for c in doubles if c not in free]
            info['repair_removed_column']=removed
            info['free_double_count']=free_count
            info['clauses']=len(clauses)
        generated=time.monotonic()-began
        pipe.send({'event':'encoded','encoding_seconds':generated,**info})
        with Solver(name=solver_name,bootstrap_with=clauses) as solver:
            if phases is not None:solver.set_phases(phases)
            sat=solver.solve()
            result={'status':'SAT' if sat else 'UNSAT','solver':solver_name,
                    'pysat_version':pysat.__version__,'encoding_seconds':generated,
                    'total_seconds':time.monotonic()-began,'info':info,
                    'solver_stats':solver.accum_stats()}
            if sat:
                model=set(solver.get_model())
                black=sum(1<<p for p in range(7*w) if p+1 in model)
                assert black.bit_count()==w+12
                assert collision(rects,black) is None
                points=sorted((p%w+1,p//w+1) for p in bits(black))
                result['witness_one_based']=points
                result['column_word']=','.join(''.join(str(r) for c,r in points if c==x)
                                               for x in range(1,w+1))
            pipe.send({'event':'result',**result})
    except BaseException:
        pipe.send({'event':'error','traceback':traceback.format_exc()})
    finally:
        pipe.close()


def main():
    w=int(sys.argv[1])
    part=tuple(int(x)-1 for x in sys.argv[2].split(','))
    assert len(part)==3 and len(set(part))==3 and all(0<=r<7 for r in part)
    cap=float(sys.argv[3]) if len(sys.argv)>3 else 180
    solver=sys.argv[4] if len(sys.argv)>4 else 'cadical195'
    tail=[a for a in sys.argv[5:] if a!='compact']
    repair=tuple(map(int,tail[0].split(':'))) if tail else None
    compact='compact' in sys.argv[5:]
    receive,send=mp.Pipe(duplex=False)
    process=mp.Process(target=worker,args=(send,w,part,solver,repair,compact))
    began=time.monotonic()
    process.start()
    send.close()
    final=None
    encoded=None
    while process.is_alive() and time.monotonic()-began<cap:
        try:
            ready=receive.poll(min(1,max(0,cap-(time.monotonic()-began))))
        except (EOFError,OSError):
            break
        if ready:
            try:event=receive.recv()
            except EOFError:break
            print(json.dumps(event),flush=True)
            if event['event']=='encoded':encoded=event
            elif event['event']=='result':final=event
            elif event['event']=='error':final={'status':'error',**event}
    if process.is_alive():
        process.terminate()
    process.join(5)
    while True:
        try:
            if not receive.poll():break
        except (EOFError,OSError):
            break
        try:event=receive.recv()
        except (EOFError,OSError):break
        if event['event']=='result':final=event
        elif event['event']=='error':final={'status':'error',**event}
    if final is None:final={'status':'unknown','reason':'wall-clock cap','encoded':encoded}
    output={'rows':7,'columns':w,'target_black_points':w+12,
            'partition_one_based':[[r+1 for r in part],[r+1 for r in range(7) if r not in part]],
            'cap_seconds':cap,'wall_seconds':time.monotonic()-began,
            'repair_restriction':repair,'compact_axis_rivals':compact,**final}
    tag=''.join(str(r+1) for r in part)
    suffix=f'_repair{repair[0]}_free{repair[1]}' if repair else ''
    if compact:suffix+='_compact'
    (HERE/f'equality_h7_w{w}_p{tag}_{solver}{suffix}.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output),flush=True)


if __name__=='__main__':
    mp.freeze_support()
    main()
