"""Bounded lazy SAT for every parity edge at x=spacing*j, configurable sea.

The checker enumerates all potentially weak tilted rectangles. Axis rectangles
are automatically identifying because the distinct doubles form K_odd,even.
All learned clauses are positive-black-support obstructions, using the proved
no-hidden theorem when a prospective white corner changes color.
"""
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import json
import multiprocessing as mp
import sys
import time
import traceback

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'.runtime'))


@lru_cache(None)
def shapes(h):
    out=[]
    for b in range(1,h):
        for d in range(1,h-b):
            for a in range(1,b*d+1):
                if b*d%a:continue
                c=b*d//a
                for r in range(b,h-d):
                    out.append(((0,r),(a,r-b),(c,r+d),(a+c,r-b+d)))
    return out


def weak_templates(h,w,high_allowed=False,free_allowed=False,spacing=4):
    out=set()
    for sh in shapes(h):
        span=max(x for x,r in sh)
        for left in range(w-span):
            corners=tuple(sorted((left+x,r) for x,r in sh))
            if free_allowed or sum(x%spacing==0 or r==0 or (high_allowed and r==h-1) for x,r in corners)>=2:out.add(corners)
    return sorted(out)


def obstructions(templates,cols):
    """Return exact black supports for all observed hidden/colliding tilts."""
    out=set();seen={}
    for R in templates:
        black=frozenset((x,r) for x,r in R if r in cols[x])
        if len(black)<2:continue
        white=frozenset(R)-black
        if not white:
            out.add(black);continue
        if white in seen:
            out.add(black|seen[white])
        else:seen[white]=black
        P=sorted(white)
        if len(P)==1:
            x,r=P[0]
            for s in cols[x]:
                if (s-r)%2:out.add(black|{(x,s)})
        else:
            (x,r),(z,s)=P
            if x==z:
                if (r-s)%2:out.add(black)
            elif r==s:
                for t in cols[x]&cols[z]:out.add(black|{(x,t),(z,t)})
            elif s in cols[x] and r in cols[z]:out.add(black|{(x,s),(z,r)})
    return out


def worker(send,h,solver_name,seed,high_budget,free_sea,odd_sea,warm_path,empty_sea,pin_path,blocked_path,spacing,period_mask):
    try:
        from pysat.solvers import Solver
        from pysat.card import CardEnc,EncType
        from pysat.formula import IDPool
        edges=[(a,b) for a,b in combinations(range(h),2) if (a-b)%2]
        q=len(edges);w=spacing*q-spacing+1;pool=IDPool();clauses=[]
        p={(j,e):pool.id(('edge',j,e)) for j in range(q) for e in range(q)}
        for j in range(q):
            clauses+=CardEnc.equals([p[j,e] for e in range(q)],1,vpool=pool,
                                    encoding=EncType.seqcounter).clauses
        for e in range(q):
            clauses+=CardEnc.equals([p[j,e] for j in range(q)],1,vpool=pool,
                                    encoding=EncType.seqcounter).clauses
        row={(j,r):pool.id(('row',j,r)) for j in range(q) for r in range(h)}
        for j in range(q):
            for r in range(h):
                inc=[p[j,e] for e,E in enumerate(edges) if r in E]
                clauses.append([-row[j,r]]+inc)
                clauses.extend([-v,row[j,r]] for v in inc)
        high={x:pool.id(('high',x)) for x in range(w) if x%spacing} if high_budget and not free_sea else {}
        sea_domain=list(range(0,h,2)) if odd_sea else list(range(h))
        sea={(x,r):pool.id(('sea',x,r)) for x in range(w) if x%spacing for r in sea_domain} if free_sea else {}
        if sea:
            for x in range(w):
                if x%spacing:
                    clauses+=CardEnc.equals([sea[x,r] for r in sea_domain],1,vpool=pool,
                                            encoding=EncType.seqcounter).clauses
            clauses+=CardEnc.atmost([-sea[x,0] for x in range(w) if x%spacing],high_budget,
                                    vpool=pool,encoding=EncType.seqcounter).clauses
        if high:
            clauses+=CardEnc.atmost(list(high.values()),high_budget,vpool=pool,
                                    encoding=EncType.seqcounter).clauses
        if period_mask is not None:
            assert high and not free_sea and not empty_sea
            assert 0<=period_mask<1<<(spacing-1)
            clauses.extend([v if period_mask>>(x%spacing-1)&1 else -v] for x,v in high.items())
        if blocked_path:
            assert spacing==4,'learned frame constraints are specific to spacing four'
            assert h%2==1,'vertical reflection must preserve the learned odd-row sea domain'
            learned_patterns=json.loads((HERE/blocked_path).read_text())['patterns']
            for pattern in learned_patterns:
                span=pattern['span_slots'];entries=pattern['entries']
                for horizontal in (False,True):
                    for vertical in (False,True):
                        for shift in range(q-span+1):
                            clause=[]
                            for entry in entries:
                                j=span-1-entry['slot'] if horizontal else entry['slot']
                                if 'edge' in entry:
                                    edge=tuple(sorted(h-r if vertical else r-1 for r in entry['edge']))
                                    clause.append(-p[shift+j,edges.index(edge)])
                                else:
                                    r=h-entry['row'] if vertical else entry['row']-1
                                    clause.append(-row[shift+j,r])
                            clauses.append(clause)
        clauses.append([p[j,0] for j in range((q+1)//2)])
        if pin_path:
            saved=json.loads((HERE/pin_path).read_text())
            witness=next(e for e in saved['events'] if e.get('status')=='SAT')
            pin_order=[edges.index(tuple(r-1 for r in E)) for E in witness['order_one_based']]
            clauses.extend([p[j,e]] for j,e in enumerate(pin_order))
            unary_path=HERE/(Path(pin_path).stem+'_unary.json')
            if unary_path.exists() and sea:
                unary=json.loads(unary_path.read_text())
                for x,r in unary['forbidden_sea_points']:
                    if (x,r-1) in sea:clauses.append([-sea[x,r-1]])
        templates=weak_templates(h,w,bool(high),bool(sea),spacing)
        send.send({'event':'encoded','height':h,'width':w,'edges':q,
                   'high_sea_budget':high_budget,
                   'free_sea':free_sea,
                   'odd_sea':odd_sea,
                   'empty_sea':empty_sea,
                   'pinned_order':pin_path,
                   'blocked_patterns':blocked_path,
                   'spacing':spacing,
                   'period_mask':period_mask,
                   'variables':pool.top,'initial_clauses':len(clauses),
                   'potentially_weak_tilts':len(templates)})
        learned=set();iterations=0;began=time.monotonic()
        with Solver(name=solver_name,bootstrap_with=clauses) as solver:
            if warm_path:
                saved=json.loads((HERE/warm_path).read_text())
                witness=next(e for e in saved['events'] if e.get('status') in ('SAT','CANDIDATE'))
                order=[edges.index(tuple(r-1 for r in E)) for E in witness['order_one_based']]
                phases=[p[j,e] for j,e in enumerate(order)]
                for (x,r),v in sea.items():
                    old=witness['columns_one_based'][x][0]-1 if witness['columns_one_based'][x] else 0
                    preferred=min(sea_domain,key=lambda a:(abs(a-old),a))
                    phases.append(v if r==preferred else -v)
                for x,v in high.items():phases.append(v if witness['columns_one_based'][x]==[h] else -v)
                solver.set_phases(phases)
            elif seed:
                import random
                order=list(range(q));random.Random(seed).shuffle(order)
                solver.set_phases([p[j,e] for j,e in enumerate(order)])
            while True:
                if not solver.solve():
                    inverse={v:(j,r+1) for (j,r),v in row.items()}
                    supports=None if high or sea else [[inverse[-v] for v in C] for C in sorted(learned)]
                    send.send({'event':'result','status':'UNSAT','iterations':iterations,
                               'learned_clauses':len(learned),'seconds':time.monotonic()-began,
                               'forbidden_slot_row_sets':supports,
                               'stats':solver.accum_stats()});return
                model=set(solver.get_model());iterations+=1
                order=[next(e for e in range(q) if p[j,e] in model) for j in range(q)]
                cols=[]
                for x in range(w):
                    if x%spacing==0:cols.append(set(edges[order[x//spacing]]))
                    elif empty_sea:cols.append(set())
                    elif sea:cols.append({next(r for r in sea_domain if sea[x,r] in model)})
                    else:cols.append({h-1 if high.get(x) in model else 0})
                bad=obstructions(templates,cols)
                if not bad:
                    send.send({'event':'result','status':'SAT','iterations':iterations,
                               'learned_clauses':len(learned),'seconds':time.monotonic()-began,
                               'high_sea_columns_zero_based':[x for x in high if high[x] in model],
                               'nonconstant_sea_zero_based':[[x,next(iter(cols[x]))+1]
                                                            for x in range(w) if x%spacing and cols[x] and cols[x]!={0}],
                               'order_one_based':[[r+1 for r in edges[e]] for e in order],
                               'columns_one_based':[[r+1 for r in sorted(C)] for C in cols],
                               'stats':solver.accum_stats()});return
                old=len(learned)
                for support in bad:
                    literals=set()
                    for x,r in support:
                        if x%spacing==0:literals.add(-row[x//spacing,r])
                        elif sea:literals.add(-sea[x,r])
                        elif x in high:
                            assert r in (0,h-1)
                            literals.add(high[x] if r==0 else -high[x])
                        else:assert r==0
                    clause=tuple(sorted(literals))
                    if clause not in learned:
                        learned.add(clause);solver.add_clause(clause)
                assert len(learned)>old
                if iterations%10==1:
                    send.send({'event':'progress','iterations':iterations,
                               'learned_clauses':len(learned),'violations':len(bad),
                               'seconds':time.monotonic()-began})
    except BaseException:send.send({'event':'error','traceback':traceback.format_exc()})
    finally:send.close()


def main():
    h=int(sys.argv[1]);assert h>=4
    cap=float(sys.argv[2]) if len(sys.argv)>2 else 300
    solver=sys.argv[3] if len(sys.argv)>3 else 'cadical195'
    seed=int(sys.argv[4]) if len(sys.argv)>4 else 0
    high_budget=int(sys.argv[5]) if len(sys.argv)>5 else 0
    odd_sea='odd' in sys.argv[6:]
    empty_sea='empty' in sys.argv[6:]
    free_sea='free' in sys.argv[6:] or odd_sea
    warm_path=next((a[5:] for a in sys.argv[6:] if a.startswith('warm=')),None)
    pin_path=next((a[4:] for a in sys.argv[6:] if a.startswith('pin=')),None)
    blocked_path=next((a[8:] for a in sys.argv[6:] if a.startswith('blocked=')),None)
    spacing=int(next((a[8:] for a in sys.argv[6:] if a.startswith('spacing=')),'4'))
    period_mask=next((int(a[8:]) for a in sys.argv[6:] if a.startswith('pattern=')),None)
    assert spacing>=1
    assert high_budget>=0
    receive,send=mp.Pipe(duplex=False)
    child=mp.Process(target=worker,args=(send,h,solver,seed,high_budget,free_sea,odd_sea,warm_path,empty_sea,pin_path,blocked_path,spacing,period_mask))
    began=time.monotonic();child.start();send.close();events=[]
    def accept(event):
        events.append(event)
        print(json.dumps({k:v for k,v in event.items() if k not in
                          ('columns_one_based','order_one_based','forbidden_slot_row_sets')}),flush=True)
    while child.is_alive() and time.monotonic()-began<cap:
        try:
            if receive.poll(min(1,max(0,cap-time.monotonic()+began))):accept(receive.recv())
        except (EOFError,OSError):break
    if child.is_alive():child.terminate()
    child.join(5)
    while True:
        try:
            if not receive.poll():break
            accept(receive.recv())
        except (EOFError,OSError):break
    final=next((e for e in reversed(events) if e['event'] in ('result','error')),None)
    out={'height':h,'cap_seconds':cap,'solver':solver,'seed':seed,'high_sea_budget':high_budget,'free_sea':free_sea,'odd_sea':odd_sea,'warm_path':warm_path,'empty_sea':empty_sea,'pin_path':pin_path,'blocked_path':blocked_path,'spacing':spacing,'period_mask':period_mask,
         'wall_seconds':time.monotonic()-began,'status':final.get('status','error') if final else 'unknown',
         'events':events}
    suffix='_empty' if empty_sea else f'_odd{high_budget}' if odd_sea else f'_free{high_budget}' if free_sea else f'_high{high_budget}' if high_budget else ''
    if spacing!=4:suffix+=f'_s{spacing}'
    if period_mask is not None:suffix+=f'_mask{period_mask}'
    if pin_path:suffix+='_pinned'
    (HERE/f'constant_sea_h{h}_{solver}_seed{seed}{suffix}.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='events'}),flush=True)


if __name__=='__main__':mp.freeze_support();main()
