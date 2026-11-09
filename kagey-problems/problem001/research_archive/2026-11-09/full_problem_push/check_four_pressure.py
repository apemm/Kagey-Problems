"""Compare the native four-support count with the independent sea compiler."""
from pathlib import Path
import importlib.util
import json
import time

root=Path(__file__).resolve().parent
path=root.parent.parent/'2026-11-08'/'dominance_bridge'/'sea_sparse_automaton.py'
spec=importlib.util.spec_from_file_location('independent_sea_patterns',path)
sea=importlib.util.module_from_spec(spec)
spec.loader.exec_module(sea)

def allowed(phase,x,y):
    if phase==0:
        return y%2==0
    if phase==1:
        return (x+y)%2==0
    return ((x*(x-1)//2)+(y*(y-1)//2))%2==0

results=[]
for h in (4,8):
    native=json.loads((root/f'protected_four_pressure_h{h}.json').read_text())
    phase_counts=[]
    for phase in range(3):
        part=None if phase<2 else {r for r in range(1,h+1) if r*(r-1)//2%2==0}
        patterns,details=sea.forbidden_patterns(h,time.monotonic()+180,part)
        counts={}
        for size in (2,4,6):
            counts[size]=sum(all(allowed(phase,x+shift,y) for x,y in p)
                             for p in patterns if len(p)==size for shift in range(4))
        expected=native['four_times_hidden_count'][phase]+native['four_times_mixed_count'][phase]
        assert counts[2]==0,(h,phase,counts)
        assert counts[4]==expected,(h,phase,counts,expected)
        phase_counts.append(counts)
    results.append({'height':h,'phase_counts_four_times':phase_counts,'status':'PASS'})
out={'status':'PASS','checks':results}
(root/'check_four_pressure.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
