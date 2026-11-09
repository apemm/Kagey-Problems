"""Calibrate the equality CNF against a stored valid width-21 board."""
from pathlib import Path
import json
from seven_row_equality_sat import encode

HERE=Path(__file__).resolve().parent
PROBLEM=HERE.parents[2]
source=json.loads((PROBLEM/'research/2026-11-07/data/res_h7_w21_p246.json').read_text())
w=21
word=[sum(1<<(int(r)-1) for r in c) for c in source['word'].split(',')]
part=(1,3,5)
other=[r for r in range(7) if r not in part]
edges=sorted((1<<a)|(1<<b) for a in part for b in other)
types=[1<<r for r in range(7)]+edges
compact='compact' in __import__('sys').argv
clauses,rects,info=encode(w,part,compact=compact)
truth={r*w+c+1 for c,b in enumerate(word) for r in range(7) if b>>r&1}
truth|={7*w+19*c+types.index(b)+1 for c,b in enumerate(word)}
assert all(any(v in truth if v>0 else -v not in truth for v in clause) for clause in clauses)
out={'status':'passed','known_witness_width':21,'known_black_points':33,
     'clauses_checked':len(clauses),'variables':info['variables'],
     'compact_axis_rivals':compact,'source_column_word':source['word'],'info':info}
name='equality_encoder_compact_calibration.json' if compact else 'equality_encoder_calibration.json'
(HERE/name).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
