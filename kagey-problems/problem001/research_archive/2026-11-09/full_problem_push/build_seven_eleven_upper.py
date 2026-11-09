"""Complete 21-point axis family on 7 by 11, by adding one singleton.

Every such board has no empty column and excess ten. Its nonsingleton
family is either ten doubles or the unique-triple boundary core.
"""
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from solver.enumerate import rectangles


def reflect(p):
    return tuple(sorted(sum(1<<(6-r) for r in range(7) if b>>r&1) for b in p))


patterns=set()
for p in json.loads((HERE/'seven_ten_20_data.json').read_text())['patterns']:
    for row in range(7):
        q=tuple(sorted(p+[1<<row]))
        patterns.add(min(q,reflect(q)))
allrects=rectangles(7,11)
groups=[[] for _ in range(11)]
for R in allrects:
    if len({x for x,y in R})==2 and len({y for x,y in R})==2:
        continue
    points=sorted((x-1,y-1) for x,y in R)
    groups[max(x for x,y in points)].append([v for p in points for v in p])
data={'rows':7,'columns':11,'black_points':21,'output_tag':'seven_eleven_21',
      'patterns':sorted(patterns),'templates_by_last_column':groups,
      'representatives':len(patterns),'rectangles':len(allrects),
      'tilted_rectangles':sum(map(len,groups))}
(HERE/'seven_eleven_21_data.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
print(json.dumps({k:v for k,v in data.items() if k not in ('patterns','templates_by_last_column')}))
