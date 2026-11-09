"""Compare the owner CNF with full rectangle identification on fixed boards."""
from pathlib import Path
import json
import random
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'.runtime'))
sys.path.insert(0,str(HERE.parents[2]))
from pysat.solvers import Solver
from seven_row_general_sat import owner_encoding
from verify_narrow import collision
from solver.enumerate import rectangles

sources=['seven_eleven_exact_check.json','seven_row_lower_w12_b21.json','seven_row_lower_w13_b22.json']
rng=random.Random(20261109)
results=[]
for source in sources:
    data=json.loads((HERE/source).read_text())
    w=data['columns'];n=7*w
    given=set(map(tuple,data['witness_one_based']))
    target=len(given)
    clauses,rects,info=owner_encoding(w,target,3)
    independent=[sum(1<<((r-1)*w+c-1) for c,r in R) for R in rectangles(7,w)]
    assert set(rects)==set(independent)
    base={(r-1)*w+c-1 for c,r in given}
    cases=[]
    for horizontal in (False,True):
        for vertical in (False,True):
            cases.append({((6-p//w) if vertical else p//w)*w+((w-1-p%w) if horizontal else p%w) for p in base})
    for _ in range(200):
        k=rng.randint(1,5)
        chosen=base-set(rng.sample(sorted(base),k))
        chosen.update(rng.sample(sorted(set(range(n))-base),k))
        cases.append(chosen)
    valid_count=0
    with Solver(name='cadical195',bootstrap_with=clauses) as solver:
        for chosen in cases:
            mask=sum(1<<p for p in chosen)
            actual=collision(rects,mask) is None
            result=solver.solve(assumptions=[p+1 if p in chosen else -p-1 for p in range(n)])
            assert result==actual,(w,chosen,result,actual)
            valid_count+=actual
    results.append({'width':w,'black_points':target,'cases':len(cases),
                    'valid_cases':valid_count,'clauses':len(clauses),
                    'independent_rectangles':len(rects)})
out={'status':'passed','results':results,'total_fixed_boards':sum(r['cases'] for r in results)}
(HERE/'pair_owner_sat_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
