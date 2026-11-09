"""Calibrate fixed-core geometry and crop cardinalities on valid boards."""
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
PROBLEM=HERE.parents[2]
sys.path.insert(0,str(HERE/'.runtime'))
sys.path.insert(0,str(PROBLEM))
from pysat.solvers import Solver
from fixed_row_core_sat import encode
from verify_narrow import rectangles,axis_rectangles,collision

cases=[]
for name in ('seven_eleven_exact_check.json','seven_row_lower_w12_b21.json','seven_row_lower_w13_b22.json'):
    data=json.loads((HERE/name).read_text())
    w=data['columns']
    cases.append((w,[sum(1<<(r-1) for c,r in data['witness_one_based'] if c==x) for x in range(1,w+1)]))
known=json.loads((PROBLEM/'research/2026-11-07/data/res_h7_w21_p246.json').read_text())
cases.append((21,[sum(1<<(int(r)-1) for r in c) for c in known['word'].split(',')]))
# Include an actual empty-column board, when a white-column insertion is valid.
w,word=cases[0]
for at in range(w+1):
    inserted=word[:at]+[0]+word[at:]
    black=sum(1<<(r*(w+1)+c) for c,b in enumerate(inserted) for r in range(7) if b>>r&1)
    if collision(rectangles(7,w+1),black) is None:
        cases.append((w+1,inserted));break
assert len(cases)==5
records=[]
for w,word in cases:
    record={'masks':sorted(b for b in word if b.bit_count()>=2),'empty_columns':word.count(0)}
    assert record['empty_columns']<=1
    rects=rectangles(7,w);axis=set(axis_rectangles(7,w));flags=[R not in axis for R in rects]
    clauses,info=encode(w,record,rects,flags,crop=True)
    base=([0] if record['empty_columns'] else [])+[1<<r for r in range(7)]
    types=base+record['masks'];nt=len(types);n=7*w
    literals=[r*w+c+1 if b>>r&1 else -r*w-c-1 for c,b in enumerate(word) for r in range(7)]
    literals += [n+nt*c+types.index(b)+1 for c,b in enumerate(word)]
    # The fixed chosen core may lie on the other side of the symmetry cut.
    selected=word.index(record['masks'][0])
    if selected>(w-1)//2:
        word=list(reversed(word))
        literals=[r*w+c+1 if b>>r&1 else -r*w-c-1 for c,b in enumerate(word) for r in range(7)]
        literals += [n+nt*c+types.index(b)+1 for c,b in enumerate(word)]
    with Solver(name='cadical195',bootstrap_with=clauses) as solver:
        assert solver.solve(assumptions=literals)
    records.append({'width':w,'black_points':sum(b.bit_count() for b in word),
                    'triple_columns':sum(b.bit_count()==3 for b in word),
                    'empty_columns':word.count(0),'clauses':len(clauses)})
out={'status':'passed','cases':records}
(HERE/'fixed_core_sat_calibration.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
