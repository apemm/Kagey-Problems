"""Inspect deleting one singleton from the stored width-21 equality board."""
from pathlib import Path
import json
import sys
from collections import Counter

HERE=Path(__file__).resolve().parent
PROBLEM=HERE.parents[2]
sys.path.insert(0,str(PROBLEM))
from verify_narrow import rectangles

word=json.loads((PROBLEM/'research/2026-11-07/data/res_h7_w21_p246.json').read_text())['word'].split(',')
rects=rectangles(7,20)
records=[]
for i,column in enumerate(word):
    if len(column)!=1:continue
    shortened=word[:i]+word[i+1:]
    black=sum(1<<((int(r)-1)*20+c) for c,s in enumerate(shortened) for r in s)
    counts=Counter(R&~black for R in rects)
    records.append({'removed_column':i+1,'removed_row':int(column),
                    'colliding_rectangle_pairs':sum(n*(n-1)//2 for n in counts.values()),
                    'column_word':','.join(shortened)})
records.sort(key=lambda x:x['colliding_rectangle_pairs'])
(HERE/'seven_row_twenty_repair_candidates.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps([{k:v for k,v in r.items() if k!='column_word'} for r in records]))
