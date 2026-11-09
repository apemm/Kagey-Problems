"""Generate an 18-point search family by deleting from the 19-point axis family."""
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
data=json.loads((HERE/'seven_nine_search_data.json').read_text())
patterns=set()
for pattern in data['patterns']:
    for i,mask in enumerate(pattern):
        for r in range(7):
            if not mask>>r&1:
                continue
            candidate=tuple(sorted(pattern[:i]+pattern[i+1:]+[mask^(1<<r)]))
            if len(set(candidate))!=9:
                continue
            patterns.add(candidate)
data['patterns']=sorted(patterns)
data['black_points']=18
data['output_tag']='seven_nine_lower'
data['scope']='lower-bound witness search only; no completeness claim'
(HERE/'seven_nine_lower_data.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
print(json.dumps({'18_point_patterns':len(patterns)}))
