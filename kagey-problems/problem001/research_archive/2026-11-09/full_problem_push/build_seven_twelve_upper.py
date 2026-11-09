"""Complete 22-point axis family on 7 by 12.

With no empty column, remove a singleton to obtain the complete 7x11/21
family. With one empty column, the other eleven columns are all doubles
and their graph is K_3,4 minus one edge. Two empty columns are impossible.
"""
from itertools import combinations
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from solver.enumerate import rectangles


def reflect(p):
    return tuple(sorted(sum(1<<(6-r) for r in range(7) if b>>r&1) for b in p))


patterns=set()
for p in json.loads((HERE/'seven_eleven_21_data.json').read_text())['patterns']:
    for row in range(7):
        q=tuple(sorted(p+[1<<row]))
        patterns.add(min(q,reflect(q)))
for side in combinations(range(7),3):
    other=[r for r in range(7) if r not in side]
    edges=[(1<<a)|(1<<b) for a in side for b in other]
    for missing in range(12):
        q=tuple(sorted([0]+edges[:missing]+edges[missing+1:]))
        patterns.add(min(q,reflect(q)))
allrects=rectangles(7,12)
groups=[[] for _ in range(12)]
for R in allrects:
    if len({x for x,y in R})==2 and len({y for x,y in R})==2:continue
    points=sorted((x-1,y-1) for x,y in R)
    groups[max(x for x,y in points)].append([v for p in points for v in p])
data={'rows':7,'columns':12,'black_points':22,'output_tag':'seven_twelve_22',
      'patterns':sorted(patterns),'templates_by_last_column':groups,
      'representatives':len(patterns),'rectangles':len(allrects),
      'tilted_rectangles':sum(map(len,groups))}
(HERE/'seven_twelve_22_data.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
print(json.dumps({k:v for k,v in data.items() if k not in ('patterns','templates_by_last_column')}))
