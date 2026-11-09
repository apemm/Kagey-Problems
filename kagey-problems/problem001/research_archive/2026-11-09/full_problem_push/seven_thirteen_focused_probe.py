"""Focused 23-point family: reduce one triple and add two double columns."""
from itertools import combinations,combinations_with_replacement
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from solver.enumerate import rectangles


def valid(columns):
    owner={}
    for j,mask in enumerate(columns):
        for pair in combinations([r for r in range(7) if mask>>r&1],2):
            if pair in owner:return False
            owner[pair]=j
    for a,b,c in combinations(range(7),3):
        values=[owner.get(p) for p in ((a,b),(a,c),(b,c))]
        if None not in values and len(set(values))==3:return False
    return True


def reflect(p):
    return tuple(sorted(sum(1<<(6-r) for r in range(7) if b>>r&1) for b in p))


word=json.loads((HERE/'seven_eleven_20_probe_0.json').read_text())['witness_column_masks']
fixed=[b for b in word if b.bit_count()>=2]
pairs=[(1<<a)|(1<<b) for a,b in combinations(range(7),2)]
cores=set()
for index,mask in enumerate(fixed):
    if mask.bit_count()!=3:continue
    for r in range(7):
        if not mask>>r&1:continue
        smaller=fixed[:index]+[mask^(1<<r)]+fixed[index+1:]
        for a,b in combinations(pairs,2):
            core=tuple(sorted(smaller+[a,b]))
            if valid(core):cores.add(core)
patterns=set()
for core in cores:
    for singles in combinations_with_replacement(range(7),4):
        p=tuple(sorted(list(core)+[1<<r for r in singles]))
        patterns.add(min(p,reflect(p)))
groups=[[] for _ in range(13)]
allrects=rectangles(7,13)
for R in allrects:
    if len({x for x,y in R})==2 and len({y for x,y in R})==2:continue
    points=sorted((x-1,y-1) for x,y in R)
    groups[max(x for x,y in points)].append([v for p in points for v in p])
data={'rows':7,'columns':13,'black_points':23,'output_tag':'seven_thirteen_23_probe',
      'patterns':sorted(patterns),'templates_by_last_column':groups,
      'known_width_upper':{0:0,9:17,10:18,11:20,12:21},
      'nonsingleton_cores':len(cores),'representatives':len(patterns),
      'scope':'focused construction family only','rectangles':len(allrects)}
(HERE/'seven_thirteen_23_probe_data.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
print(json.dumps({k:v for k,v in data.items() if k not in ('patterns','templates_by_last_column')}))
