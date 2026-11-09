"""Compare every frozen transition against the complete original height-six graph."""
from pathlib import Path
from hashlib import sha256
import json, struct
import numpy as np
root=Path(__file__).resolve().parent
raw=root/'sea_frozen_h6_test.raw'
status=json.loads((root/'sea_frozen_h6_test.status.json').read_text())
with raw.open('rb') as f:
    magic,h,n,original=struct.unpack('<iiii',f.read(16))
    checkpoint_sha=f.read(32).hex()
    residual_sha=f.read(32).hex()
assert magic==0x53454631 and h==6 and status['processed_sources']==n
assert raw.stat().st_size==80+4*h*n
assert status['checkpoint_sha256']==checkpoint_sha
assert status['residual_sha256']==residual_sha
actual=np.memmap(raw,mode='r',dtype='<i4',offset=80,shape=(n,h))
complete=root/'sea_packed_h6.bin'
with complete.open('rb') as f:
    gm,gh,gn=struct.unpack('<iii',f.read(12))
assert gm==0x53454731 and gh==h and gn>=n
old=np.memmap(complete,mode='r',dtype='<i4',offset=12,shape=(gn,h))
expected=np.array(old[:n],copy=True)
expected[expected>=n]=-1
assert np.array_equal(actual,expected)
record=dict(status='PASS',height=h,states=n,original_processed=original,
            transitions_checked=n*h,resume_boundary=11000,
            raw_sha256=sha256(raw.read_bytes()).hexdigest(),
            original_graph_sha256=sha256(complete.read_bytes()).hexdigest(),
            source_sha256={name:sha256((root/name).read_bytes()).hexdigest()
                           for name in ['SeaFrozenStorage.cs','SeaGraphFrozen.cs',
                                        'build_frozen_sea.py','run_frozen_sea_graph.ps1']})
(root/'sea_frozen_h6_independent_check.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
