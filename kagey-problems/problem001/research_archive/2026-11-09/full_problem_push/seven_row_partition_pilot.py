"""Run a fixed time cap on each nonparity reflection class of partitions."""
from itertools import combinations
from pathlib import Path
import json
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
w=int(sys.argv[1]) if len(sys.argv)>1 else 20
cap=float(sys.argv[2]) if len(sys.argv)>2 else 10
solver=sys.argv[3] if len(sys.argv)>3 else 'cadical195'
compact='compact' in sys.argv[4:]
suffix='_compact' if compact else ''
parts=[p for p in combinations(range(1,8),3) if p<=tuple(sorted(8-r for r in p)) and p!=(2,4,6)]
assert len(parts)==18
records=[]
began=time.monotonic()
for part in parts:
    tag=''.join(map(str,part))
    path=HERE/f'equality_h7_w{w}_p{tag}_{solver}{suffix}.json'
    command=[sys.executable,str(HERE/'seven_row_equality_sat.py'),str(w),
             ','.join(map(str,part)),str(cap),solver]
    if compact:command.append('compact')
    if path.exists():
        completed=None
    else:
        completed=subprocess.run(command,capture_output=True,text=True,timeout=cap+15)
        (HERE/f'equality_h7_w{w}_p{tag}_{solver}{suffix}.log').write_text(completed.stdout+completed.stderr)
    if (completed is not None and completed.returncode) or not path.exists():
        record={'partition':part,'status':'error','returncode':completed.returncode}
    else:
        result=json.loads(path.read_text())
        record={'partition':part,'status':result['status'],'wall_seconds':result['wall_seconds']}
        if result['status']=='SAT':record['column_word']=result['column_word']
    records.append(record)
    print(json.dumps(record),flush=True)
out={'width':w,'partitions':18,'cap_per_partition':cap,'solver':solver,
     'compact_axis_rivals':compact,
     'elapsed_seconds':time.monotonic()-began,'records':records,
     'scope':'all nonparity balanced partitions up to vertical reflection; each cap may be unknown'}
(HERE/f'equality_h7_w{w}_nonparity_pilot_{solver}{suffix}.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)
