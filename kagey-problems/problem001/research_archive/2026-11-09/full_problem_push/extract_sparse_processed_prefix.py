"""Stream a fully processed induced subgraph from a format-five checkpoint."""
from hashlib import sha256
from pathlib import Path
import argparse
import json
import struct
import time
import numpy as np

def digest(path):
    out = sha256()
    with path.open('rb') as stream:
        while chunk := stream.read(8*1024*1024):
            out.update(chunk)
    return out.hexdigest()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('checkpoint',type=Path)
    parser.add_argument('residuals',type=Path)
    parser.add_argument('output',type=Path)
    args = parser.parse_args()
    began = time.monotonic()
    with args.checkpoint.open('rb') as stream:
        magic,h,words = struct.unpack('<iii',stream.read(12))
        assert magic == 0x53454135
        fingerprint = stream.read(32).hex()
        assert fingerprint == digest(args.residuals)
        discovered,processed,edge_count = struct.unpack('<iii',stream.read(12))
        assert 0 < processed <= discovered and edge_count == processed*h
        blocks, = struct.unpack('<i',stream.read(4))
        assert blocks > 0
        stream.seek(32*blocks,1)
        sparse_bytes, = struct.unpack('<q',stream.read(8))
        assert sparse_bytes >= 0
        stream.seek(sparse_bytes+16*discovered,1)
        edge_offset = stream.tell()
        assert args.checkpoint.stat().st_size == edge_offset+4*edge_count
    if args.output.exists():
        raise FileExistsError(args.output)
    with args.output.open('wb') as stream:
        stream.write(struct.pack('<iii',0x53454731,h,processed))
        stream.truncate(12+4*edge_count)
    source = np.memmap(args.checkpoint,mode='r',dtype='<i4',
                       offset=edge_offset,shape=(processed,h))
    target = np.memmap(args.output,mode='r+',dtype='<i4',
                       offset=12,shape=(processed,h))
    dropped = kept = 0
    outdegrees = np.zeros(h+1,dtype=np.int64)
    for start in range(0,processed,250000):
        stop = min(processed,start+250000)
        chunk = np.array(source[start:stop],copy=True)
        assert np.all(chunk >= -1) and np.all(chunk < discovered)
        dropped += int(np.count_nonzero(chunk >= processed))
        chunk[chunk >= processed] = -1
        kept += int(np.count_nonzero(chunk >= 0))
        outdegrees += np.bincount(np.count_nonzero(chunk >= 0,axis=1),minlength=h+1)
        target[start:stop] = chunk
    target.flush()
    del source,target
    result = dict(scope='Exact processed-prefix induced subgraph; full sea graph unresolved',
                  full_graph_complete=processed==discovered,
                  checkpoint=args.checkpoint.name,checkpoint_bytes=args.checkpoint.stat().st_size,
                  checkpoint_sha256=digest(args.checkpoint),
                  residuals=args.residuals.name,residual_sha256=fingerprint,
                  height=h,words=words,discovered_states=discovered,
                  prefix_states=processed,block_pool_count=blocks,sparse_bytes=sparse_bytes,
                  checkpoint_edge_offset=edge_offset,kept_edges=kept,
                  dropped_frontier_edges=dropped,outdegree_counts=outdegrees.tolist(),
                  graph=args.output.name,graph_sha256=digest(args.output),
                  seconds=time.monotonic()-began)
    args.output.with_suffix('.extraction.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
