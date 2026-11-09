"""Check cropped-search coverage and the matching width-12 witness."""
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from solver.enumerate import rectangles

data=json.loads((HERE/'seven_twelve_22_crop_data.json').read_text())
plain=json.loads((HERE/'seven_twelve_22_data.json').read_text())
assert data['patterns']==plain['patterns']
assert len(data['patterns'])==121158
assert data['known_width_upper']=={'0':0,'9':17,'10':18,'11':20}
covered=set();chunks=[]
for name in ('seven_twelve_22_crop_0.json','seven_twelve_22_crop_42958.json'):
    result=json.loads((HERE/name).read_text())
    assert result['witness_column_masks'] is None
    entries=result['completed_patterns']
    assert [r['index'] for r in entries]==list(range(result['start_index'],result['last_index']+1))
    for r in entries:
        if r['status']=='UNSAT':covered.add(r['index'])
        else:assert r['status']=='incomplete' and r is entries[-1]
    chunks.append({'file':name,'nodes':result['nodes'],'seconds':result['seconds'],
                   'first':result['start_index'],'last':result['last_index'],'status':result['status']})
assert covered==set(range(121158))
lower=json.loads((HERE/'seven_row_lower_w12_b21.json').read_text())
black=set(map(tuple,lower['witness_one_based']))
assert len(black)==21
visible=[R-black for R in rectangles(7,12)]
assert len(visible)==len(set(visible))==1996
out={'status':'passed','rows':7,'columns':12,'exact_value':21,
     'complete_representatives':len(covered),'chunks':chunks,
     'total_nodes_including_repeated_partial_pattern':sum(c['nodes'] for c in chunks),
     'total_seconds':sum(c['seconds'] for c in chunks),
     'column_word':lower['column_word'],'verified_rectangles':1996}
(HERE/'seven_twelve_exact_check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
