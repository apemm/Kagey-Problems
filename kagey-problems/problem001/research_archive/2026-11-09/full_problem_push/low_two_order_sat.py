"""Bounded permutation search for low-two sea cores, with the full parity F."""
from itertools import combinations
from pathlib import Path
import json
import multiprocessing as mp
import sys
import time
import traceback

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'.runtime'))
from constant_sea_order_sat import shapes,obstructions

def worker(send,h,seed,omit_boundary):
    try:
        from pysat.solvers import Solver
        from pysat.card import CardEnc,EncType
        from pysat.formula import IDPool
        edges=[(a,b) for a,b in combinations(range(h),2)
               if (a-b)%2 and (not omit_boundary or a>0)]
        q=len(edges);w=4*q-3
        pool=IDPool();clauses=[]
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
        clauses.append([p[j,0] for j in range((q+1)//2)])
        templates=set()
        for sh in shapes(h):
            span=max(x for x,r in sh)
            for left in range(w-span):
                R=tuple(sorted((left+x,r) for x,r in sh))
                if sum(x%4==0 or (x%2==1 and r==0) or
                       (x%4==2 and r==1) for x,r in R)>=2:
                    templates.add(R)
        templates=sorted(templates)
        send.send(dict(phase='compiled',height=h,width=w,doubles=q,
                       templates=len(templates),variables=pool.top,clauses=len(clauses)))
        learned=set()
        with Solver(name='cadical195',bootstrap_with=clauses) as solver:
            # A deterministic cyclic matching order gives useful initial phases.
            n=(h+1)//2
            preferred=[]
            for t in range(n):
                for a in range(n):
                    A=2*a;B=2*((a+t)%n)+1
                    edge=tuple(sorted((A,B)))
                    if A<h and B<h and edge in edges:
                        preferred.append(edges.index(edge))
            assert sorted(preferred)==list(range(q))
            if seed%2:
                preferred.reverse()
            solver.set_phases([p[j,e] if e==preferred[j] else -p[j,e]
                               for j in range(q) for e in range(q)])
            iteration=0
            while solver.solve():
                iteration+=1
                model=set(solver.get_model())
                order=[next(e for e in range(q) if p[j,e] in model) for j in range(q)]
                cols=[set(edges[order[x//4]]) if x%4==0
                      else {0 if x%2 else 1} for x in range(w)]
                bad=obstructions(templates,cols)
                if not bad:
                    send.send(dict(status='SAT',iteration=iteration,width=w,doubles=q,
                                   order=[[r+1 for r in edges[e]] for e in order],
                                   columns=[[r+1 for r in sorted(C)] for C in cols],
                                   learned_clauses=len(learned),
                                   scope='Core valid against full final parity pair set; no collars asserted.'))
                    return
                added=0
                for support in bad:
                    clause=tuple(sorted({-row[x//4,r] for x,r in support if x%4==0}))
                    assert clause,('zero-label obstruction',support)
                    if clause not in learned:
                        learned.add(clause);solver.add_clause(list(clause));added+=1
                assert added
                if iteration<=5 or iteration%20==0:
                    send.send(dict(phase='refine',iteration=iteration,violations=len(bad),
                                   added=added,learned_clauses=len(learned)))
            send.send(dict(status='UNSAT',iteration=iteration,learned_clauses=len(learned),
                           scope='Specified fixed-slot low-two family only.'))
    except BaseException:
        send.send(dict(status='ERROR',traceback=traceback.format_exc()))
    finally:
        send.close()

def main():
    h=int(sys.argv[1]);cap=float(sys.argv[2]);seed=int(sys.argv[3]) if len(sys.argv)>3 else 0
    omit_boundary='full' not in sys.argv[4:]
    receive,send=mp.Pipe(False)
    child=mp.Process(target=worker,args=(send,h,seed,omit_boundary))
    started=time.monotonic();events=[]
    child.start();send.close()
    while child.is_alive() and time.monotonic()-started<cap:
        if receive.poll(.2):
            try:event=receive.recv()
            except EOFError:break
            events.append(event)
            print(json.dumps({k:v for k,v in event.items() if k not in ('order','columns')}),flush=True)
            if event.get('status'):break
    if child.is_alive():
        if events and events[-1].get('status'):child.join(2)
        if child.is_alive():child.terminate()
    child.join()
    while True:
        try:
            if not receive.poll():break
            events.append(receive.recv())
        except (EOFError,OSError):break
    if not events or not events[-1].get('status'):
        events.append(dict(status='UNKNOWN',reason='time cap'))
    result=dict(height=h,cap_seconds=cap,seed=seed,omit_row_one_edges=omit_boundary,
                events=events,seconds=time.monotonic()-started)
    name=f'low_two_core_h{h}_seed{seed}'+('' if omit_boundary else '_full')+'.json'
    (HERE/name).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(output=name,status=events[-1]['status'],seconds=result['seconds'])),flush=True)

if __name__=='__main__':main()
