"""Independent chunked integer Collatz checker for the native certificate."""
import argparse
import hashlib
import json
from pathlib import Path
import struct
import numpy as np


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('certificate',type=Path)
    args=parser.parse_args()
    cert=json.loads(args.certificate.read_text())
    root=args.certificate.parent
    graph=root/cert['graph']
    digest=hashlib.sha256()
    with graph.open('rb') as source:
        while block:=source.read(4*1024*1024):
            digest.update(block)
    assert digest.hexdigest().upper()==cert['graph_sha256']
    with graph.open('rb') as source:
        magic,h,n=struct.unpack('<iii',source.read(12))
    assert magic==0x53454731 and h==cert['height'] and n==cert['states']
    edges=np.memmap(graph,mode='r',dtype='<i4',offset=12,shape=(n,h))
    weights_path=root/cert['weights_file']
    with weights_path.open('rb') as source:
        magic,nw,cid=struct.unpack('<iii',source.read(12))
    assert magic==0x53505731 and nw==n and cid==cert['component']
    weights=np.memmap(weights_path,mode='r',dtype='<i8',offset=12,shape=(n,))
    component=np.memmap(str(graph)+'.components',mode='r',dtype='<i4',offset=4,shape=(n,))
    lower,upper,scale=(int(cert[k]) for k in ('lower_numerator','upper_numerator','scale'))
    maximum=int(weights.max())
    assert max(h*scale,lower,upper)*maximum < 2**63
    checked=0
    for start in range(0,n,250000):
        stop=min(n,start+250000)
        own=np.asarray(weights[start:stop])
        active=np.asarray(component[start:stop])==cid
        assert np.all(own[active]>0) and np.all(own[~active]==0)
        sums=np.zeros(stop-start,dtype=np.int64)
        for r in range(h):
            target=np.asarray(edges[start:stop,r])
            valid=target>=0
            assert np.all(target[valid]<n)
            sums[valid]+=weights[target[valid]]
        assert np.all(lower*own[active]<=scale*sums[active])
        assert np.all(upper*own[active]>=scale*sums[active])
        checked+=int(active.sum())
    assert checked==cert['component_size']
    result={'status':'PASS','certificate':args.certificate.name,
            'component_states_checked':checked,'lower':f'{lower}/{scale}',
            'upper':f'{upper}/{scale}','integer_arithmetic':'signed 64-bit; overflow bound checked'}
    output=args.certificate.with_suffix('.verified.json')
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))


if __name__=='__main__':
    main()
