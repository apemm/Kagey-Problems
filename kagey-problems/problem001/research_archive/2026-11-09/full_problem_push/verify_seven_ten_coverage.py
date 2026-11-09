"""Verify exhaustive chunk coverage and the matching lower-bound witness."""
from pathlib import Path
import hashlib
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from solver.enumerate import rectangles

data_path=HERE/'seven_ten_19_data.json'
data=json.loads(data_path.read_text())
assert len(data['patterns'])==463006
covered=set()
chunks=[]
for name in ('seven_ten_19_0.json','seven_ten_19_317989.json'):
    path=HERE/name
    output=json.loads(path.read_text())
    assert output['witness_column_masks'] is None
    entries=output['completed_patterns']
    assert [r['index'] for r in entries]==list(range(output['start_index'],output['last_index']+1))
    for r in entries:
        if r['status']=='UNSAT':
            covered.add(r['index'])
        else:
            assert r['status']=='incomplete' and r is entries[-1]
    chunks.append({'file':name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                   'nodes':output['nodes'],'seconds':output['seconds'],
                   'first':output['start_index'],'last':output['last_index'],
                   'status':output['status']})
assert covered==set(range(len(data['patterns'])))
lower=json.loads((HERE/'seven_ten_lower_witness.json').read_text())
black=set(map(tuple,lower['witness_one_based']))
assert len(black)==18
rects=rectangles(7,10)
visible=[R-black for R in rects]
assert len(visible)==len(set(visible))==1385
out={'status':'passed','exact_value':18,'rows':7,'columns':10,
     'complete_representatives':len(covered),'chunks':chunks,
     'data_sha256':hashlib.sha256(data_path.read_bytes()).hexdigest(),
     'total_nodes_including_repeated_partial_pattern':sum(c['nodes'] for c in chunks),
     'total_seconds':sum(c['seconds'] for c in chunks),
     'lower_column_word':lower['column_word'],'verified_rectangles':len(rects)}
(HERE/'seven_ten_coverage.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
