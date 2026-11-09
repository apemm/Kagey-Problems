"""Bounded exact Moore refinement probe for an exported partial sea DFA."""
import argparse
import json
from pathlib import Path
import struct
import time
import numpy as np

parser=argparse.ArgumentParser()
parser.add_argument('graph',type=Path)
parser.add_argument('--rounds',type=int,default=30)
args=parser.parse_args()
with args.graph.open('rb') as source:
    magic,h,n=struct.unpack('<iii',source.read(12))
assert magic==0x53454731
edges=np.memmap(args.graph,mode='r',dtype='<i4',offset=12,shape=(n,h))
labels=np.ones(n,dtype=np.int32)
history=[]
started=time.monotonic()
stable=False
for step in range(args.rounds):
    signatures=np.zeros((n,h+1),dtype=np.int32)
    signatures[:,0]=labels
    for r in range(h):
        target=np.asarray(edges[:,r])
        valid=target>=0
        signatures[valid,r+1]=labels[target[valid]]
    _,labels=np.unique(signatures,axis=0,return_inverse=True)
    labels=labels.astype(np.int32)+1
    count=int(labels.max())
    result=dict(round=step+1,classes=count,seconds=time.monotonic()-started)
    history.append(result)
    print(json.dumps(result),flush=True)
    if len(history)>1 and count==history[-2]['classes']:
        stable=True
        break
result=dict(graph=args.graph.name,states=n,stable=stable,history=history)
args.graph.with_suffix('.minimize_probe.json').write_text(json.dumps(result,indent=2)+'\n')
