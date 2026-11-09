"""Focused 20-point construction family, not a complete upper-bound family."""
from itertools import combinations,combinations_with_replacement
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
PROBLEM=HERE.parents[2]


def valid(columns):
    owner={}
    for j,mask in enumerate(columns):
        for a,b in combinations([r for r in range(7) if mask>>r&1],2):
            if (a,b) in owner:return False
            owner[a,b]=j
    for a,b,c in combinations(range(7),3):
        values=[owner.get(pair) for pair in ((a,b),(a,c),(b,c))]
        if None not in values and len(set(values))==3:return False
    return True


def reflect(p):
    return tuple(sorted(sum(1<<(6-r) for r in range(7) if b>>r&1) for b in p))


models=json.loads((PROBLEM/'jis/data/table_counts/sat_7x8_16.json').read_text())[0]['first_models']
cores=set()
for points in models:
    columns=[sum(1<<(r-1) for c,r in points if c==x) for x in range(1,9)]
    fixed=[c for c in columns if c.bit_count()>=2]
    for a,b in combinations(range(7),2):
        extended=tuple(sorted(fixed+[(1<<a)|(1<<b)]))
        if valid(extended):cores.add(extended)
patterns=set()
for core in cores:
    for singles in combinations_with_replacement(range(7),11-len(core)):
        p=tuple(sorted(list(core)+[1<<r for r in singles]))
        patterns.add(min(p,reflect(p)))
data=json.loads((HERE/'seven_eleven_21_data.json').read_text())
data.update(black_points=20,output_tag='seven_eleven_20_probe',
            patterns=sorted(patterns),representatives=len(patterns),
            nonsingleton_cores=len(cores),scope='lower-bound construction family only')
(HERE/'seven_eleven_20_probe_data.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
print(json.dumps({k:v for k,v in data.items() if k not in ('patterns','templates_by_last_column')}))
