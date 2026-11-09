"""Isolate unconditional vertical-presentation obstructions between 4j double slots."""
from itertools import combinations
from math import isqrt
from pathlib import Path
import json
import random
import sys
import threading
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'.runtime'))


def patterns(h):
    out=[]
    for d in range(1,(h-1)//4+1):
        for a,b in combinations(range(1,h+1),2):
            if (a-b)%2==0:continue
            squared=(4*d)**2+(a-b)**2;L=isqrt(squared)
            if L*L==squared and L%2 and a+b-L>=2 and a+b+L<=2*h:
                out.append((d,a,b))
    return out


def main():
    from pysat.solvers import Solver
    from pysat.card import CardEnc,EncType
    from pysat.formula import IDPool
    h=int(sys.argv[1]) if len(sys.argv)>1 else 15
    cap=float(sys.argv[2]) if len(sys.argv)>2 else 60
    E=[e for e in combinations(range(1,h+1),2) if (e[0]-e[1])%2]
    q=len(E);pool=IDPool();clauses=[]
    p={(j,e):pool.id(('edge',j,e)) for j in range(q) for e in range(q)}
    row={(j,r):pool.id(('row',j,r)) for j in range(q) for r in range(1,h+1)}
    for j in range(q):clauses+=CardEnc.equals([p[j,e] for e in range(q)],1,vpool=pool,encoding=EncType.seqcounter).clauses
    for e in range(q):clauses+=CardEnc.equals([p[j,e] for j in range(q)],1,vpool=pool,encoding=EncType.seqcounter).clauses
    for (j,r),v in row.items():
        incident=[p[j,e] for e in range(q) if r in E[e]]
        clauses.append([-v]+incident);clauses.extend([-u,v] for u in incident)
    pp=patterns(h)
    for d,a,b in pp:
        for j in range(q-d):
            clauses.append([-row[j,a],-row[j+d,b]])
            clauses.append([-row[j,b],-row[j+d,a]])
    begin=time.monotonic()
    with Solver(name='glucose4',bootstrap_with=clauses) as solver:
        order=list(range(q));random.Random(17).shuffle(order)
        solver.set_phases([p[j,e] for j,e in enumerate(order)])
        timer=threading.Timer(cap,solver.interrupt);timer.start()
        try:sat=solver.solve_limited(expect_interrupt=True)
        finally:timer.cancel()
        out={'height':h,'slots':q,'width':4*q-3,'cap_seconds':cap,
             'status':'unknown' if sat is None else 'SAT' if sat else 'UNSAT',
             'patterns':pp,'variables':pool.top,'clauses':len(clauses),
             'seconds':time.monotonic()-begin,'stats':solver.accum_stats()}
        if sat:
            model=set(solver.get_model())
            order=[E[next(e for e in range(q) if p[j,e] in model)] for j in range(q)]
            assert len(set(order))==q
            assert not any((a in order[j] and b in order[j+d]) or (b in order[j] and a in order[j+d])
                           for d,a,b in pp for j in range(q-d))
            out['order_one_based']=order
    (HERE/f'p_only_spacing4_h{h}.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__':main()
