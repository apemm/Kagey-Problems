"""Remove singleton-row choices from the complete excess-ten axis family."""
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent


def reflect(core):
    return tuple(sorted(sum(1<<(6-r) for r in range(7) if b>>r&1) for b in core))


data=json.loads((HERE/'seven_twelve_22_data.json').read_text())
cores=set()
for p in data['patterns']:
    core=tuple(b for b in p if b.bit_count()>=2)
    cores.add((min(core,reflect(core)),p.count(0)))
records=[{'masks':core,'empty_columns':empty} for core,empty in sorted(cores)]
assert len(records)==2664
out={'rows':7,'excess':10,'cores':records,'total_cores':len(records),
     'triple_cores':sum(any(b.bit_count()==3 for b in r['masks']) for r in records),
     'empty_cores':sum(r['empty_columns'] for r in records)}
(HERE/'fixed_excess_ten_cores.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='cores'}))
