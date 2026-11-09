"""Check the complete upper-bound certificate and both rectangle generators."""
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles as bit_rectangles,collision
from solver.enumerate import rectangles

upper=json.loads((HERE/'seven_eleven_21_0.json').read_text())
data=json.loads((HERE/'seven_eleven_21_data.json').read_text())
assert upper['status']=='UNSAT'
assert len(data['patterns'])==36888
assert [c['index'] for c in upper['completed_patterns']]==list(range(36888))
assert all(c['status']=='UNSAT' for c in upper['completed_patterns'])
lower=json.loads((HERE/'seven_eleven_20_probe_0.json').read_text())
assert lower['status']=='SAT'
columns=lower['witness_column_masks']
black={(c+1,r+1) for c,b in enumerate(columns) for r in range(7) if b>>r&1}
assert len(black)==20
mask=sum(1<<((r-1)*11+c-1) for c,r in black)
assert collision(bit_rectangles(7,11),mask) is None
visible=[R-black for R in rectangles(7,11)]
assert len(visible)==len(set(visible))==1680
out={'status':'passed','rows':7,'columns':11,'exact_value':20,
     'complete_upper_bound_representatives':36888,
     'upper_nodes':upper['nodes'],'upper_seconds':upper['seconds'],
     'witness_one_based':sorted(black),'column_word':lower['witness_column_word'],
     'independently_verified_rectangles':1680}
(HERE/'seven_eleven_exact_check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
