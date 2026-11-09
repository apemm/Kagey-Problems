"""Check which sizes of learned supports already rule out height nine."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'.runtime'))
from pysat.solvers import Solver
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool


def main():
    h=9;E=[e for e in combinations(range(1,h+1),2) if (e[0]-e[1])%2]
    q=len(E);pool=IDPool();clauses=[]
    p={(j,e):pool.id(('edge',j,e)) for j in range(q) for e in range(q)}
    r={(j,a):pool.id(('row',j,a)) for j in range(q) for a in range(1,h+1)}
    for j in range(q):clauses+=CardEnc.equals([p[j,e] for e in range(q)],1,vpool=pool,encoding=EncType.seqcounter).clauses
    for e in range(q):clauses+=CardEnc.equals([p[j,e] for j in range(q)],1,vpool=pool,encoding=EncType.seqcounter).clauses
    for (j,a),v in r.items():
        inc=[p[j,e] for e in range(q) if a in E[e]]
        clauses.append([-v]+inc);clauses.extend([-u,v] for u in inc)
    clauses.append([p[j,0] for j in range((q+1)//2)])
    data=json.loads((HERE/'constant_sea_h9_glucose4_seed17.json').read_text())
    supports=data['events'][-1]['forbidden_slot_row_sets']
    result=[]
    for k in (2,3,4):
        extra=[[-r[tuple(pair)] for pair in C] for C in supports if len(C)<=k]
        with Solver(name='cadical195',bootstrap_with=clauses+extra) as solver:
            sat=solver.solve();record={'maximum_support_size':k,'clauses':len(extra),'status':'SAT' if sat else 'UNSAT'}
            if sat:
                model=set(solver.get_model())
                record['order']=[E[next(e for e in range(q) if p[j,e] in model)] for j in range(q)]
            result.append(record)
    out={'support_sizes':dict(Counter(map(len,supports))),'subsets':result}
    (HERE/'constant_sea_h9_support_analysis.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__':main()
