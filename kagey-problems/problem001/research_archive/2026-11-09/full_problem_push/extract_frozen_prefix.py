"""Extract the fully committed induced prefix after a frozen run has stopped."""
from pathlib import Path
from hashlib import sha256
import argparse,json,struct,time
import numpy as np

def digest(path):
    out=sha256()
    with path.open('rb') as f:
        while block:=f.read(8*1024*1024): out.update(block)
    return out.hexdigest()

parser=argparse.ArgumentParser()
parser.add_argument('raw',type=Path)
parser.add_argument('status',type=Path)
parser.add_argument('output',type=Path)
args=parser.parse_args()
began=time.monotonic()
status=json.loads(args.status.read_text())
assert status['stop_reason'] not in ('running','initialized')
with args.raw.open('rb') as f:
    magic,h,n,original=struct.unpack('<iiii',f.read(16))
    checkpoint_sha=f.read(32).hex();residual_sha=f.read(32).hex()
assert magic==0x53454631
assert status['height']==h and status['states']==n and status['original_processed']==original
assert status['checkpoint_sha256']==checkpoint_sha and status['residual_sha256']==residual_sha
p=status['processed_sources']
assert original<=p<=n and args.raw.stat().st_size==status['committed_bytes']==80+4*h*p
if args.output.exists(): raise FileExistsError(args.output)
with args.output.open('wb') as f:
    f.write(struct.pack('<iii',0x53454731,h,p));f.truncate(12+4*h*p)
source=np.memmap(args.raw,mode='r',dtype='<i4',offset=80,shape=(p,h))
target=np.memmap(args.output,mode='r+',dtype='<i4',offset=12,shape=(p,h))
kept=dropped=0
for start in range(0,p,250000):
    stop=min(p,start+250000)
    values=np.array(source[start:stop],copy=True)
    assert np.all(values>=-1) and np.all(values<n)
    dropped+=int(np.count_nonzero(values>=p))
    values[values>=p]=-1
    kept+=int(np.count_nonzero(values>=0))
    target[start:stop]=values
target.flush();del source,target
result=dict(status='PASS',scope='Exact induced prefix of the frozen known-state model',
            full_graph_complete=False,frozen_graph_complete=p==n,
            height=h,known_states=n,processed_sources=p,original_processed=original,
            kept_edges=kept,dropped_unprocessed_targets=dropped,
            checkpoint_sha256=checkpoint_sha,residual_sha256=residual_sha,
            raw_sha256=digest(args.raw),graph_sha256=digest(args.output),
            seconds=time.monotonic()-began)
args.output.with_suffix('.extraction.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
