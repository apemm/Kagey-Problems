"""Build independent complete rectangle templates for the 18-point audit."""
from pathlib import Path
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles

groups=[[] for _ in range(9)]
for mask in rectangles(7,9):
    cells=[i for i in range(63) if mask>>i&1]
    assert len(cells)==4
    points=[(i%9,i//9) for i in cells]
    groups[max(c for c,r in points)].append([v for p in points for v in p])
assert sum(map(len,groups))==1113
(HERE/'seven_nine_all_rectangles.json').write_text(json.dumps(groups,separators=(',',':'))+'\n')
print(json.dumps({'rectangles':sum(map(len,groups)),'counts_by_last_column':list(map(len,groups))}))
