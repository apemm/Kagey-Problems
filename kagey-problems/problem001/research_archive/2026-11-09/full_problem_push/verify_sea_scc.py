"""Verify an SCC certificate by independent reachability and DAG checks.

The present certificate format covers one nonsingleton recurrent component
and singleton transient components. No SCC algorithm from the native builder
is reused. Every edge is checked against the claimed component order, and
the recurrent component is checked by reachability in both directions.
"""
import argparse
import hashlib
import json
from pathlib import Path
import struct
import time
import numpy as np


def sha256(path):
    digest=hashlib.sha256()
    with path.open('rb') as source:
        while block:=source.read(4*1024*1024):
            digest.update(block)
    return digest.hexdigest()


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('report',type=Path)
    args=parser.parse_args()
    started=time.monotonic()
    report=json.loads(args.report.read_text())
    assert report['complete']
    graph=args.report.with_suffix('.bin')
    with graph.open('rb') as source:
        magic,h,n=struct.unpack('<iii',source.read(12))
    assert magic==0x53454731 and h==report['height'] and n==report['states']
    assert graph.stat().st_size==12+4*n*h
    edges=np.memmap(graph,mode='r',dtype='<i4',offset=12,shape=(n,h))
    component_path=Path(str(graph)+'.components')
    with component_path.open('rb') as source:
        assert struct.unpack('<i',source.read(4))[0]==n
    assert component_path.stat().st_size==4+4*n
    component=np.memmap(component_path,mode='r',dtype='<i4',offset=4,shape=(n,))
    info=report['components']
    assert len(info['cyclic_components'])==1
    main=info['cyclic_components'][0]
    cid=main['id']
    counts=np.bincount(component,minlength=info['scc_count'])
    assert len(counts)==info['scc_count'] and int(counts.sum())==n
    assert counts[cid]==main['size']
    counts[cid]=1
    assert np.all(counts==1)
    count_edges=0
    chunk=250000
    for start in range(0,n,chunk):
        stop=min(n,start+chunk)
        labels=np.asarray(component[start:stop])
        for r in range(h):
            target=np.asarray(edges[start:stop,r])
            assert np.all(target>=-1) and np.all(target<n)
            valid=target>=0
            destination=component[target[valid]]
            origin=labels[valid]
            assert np.all(destination>=origin)
            assert np.all((destination!=origin)|(origin==cid))
            count_edges+=int(valid.sum())
    assert count_edges==info['edges']
    root=next(v for v in info['constant_states'] if v>=0 and component[v]==cid)
    reached=np.zeros(n,dtype=np.bool_)
    reached[root]=True
    frontier=np.array([root],dtype=np.int64)
    forward_steps=0
    while len(frontier):
        previous=reached.copy()
        for start in range(0,len(frontier),chunk):
            targets=np.asarray(edges[frontier[start:start+chunk]]).reshape(-1)
            targets=targets[targets>=0]
            targets=targets[component[targets]==cid]
            reached[targets]=True
        frontier=np.flatnonzero(reached & ~previous)
        forward_steps+=1
    assert int(reached.sum())==main['size']
    reached[:]=False
    reached[root]=True
    reverse_steps=0
    while True:
        changed=0
        for start in range(0,n,chunk):
            stop=min(n,start+chunk)
            active=(np.asarray(component[start:stop])==cid)&~reached[start:stop]
            ids=np.flatnonzero(active)+start
            if not len(ids):
                continue
            targets=np.asarray(edges[ids])
            hit=(targets>=0)&reached[np.maximum(targets,0)]
            new=ids[np.any(hit,axis=1)]
            reached[new]=True
            changed+=len(new)
        reverse_steps+=1
        if reverse_steps%5==0:
            print(json.dumps({'phase':'reverse_reachability','passes':reverse_steps,
                              'reached':int(reached.sum())}),flush=True)
        if not changed:
            break
    assert int(reached.sum())==main['size']
    result={'status':'PASS','graph':graph.name,'states':n,'edges_checked':count_edges,
            'recurrent_component_size':main['size'],'transient_singletons':n-main['size'],
            'forward_bfs_steps':forward_steps,'reverse_fixed_point_passes':reverse_steps,
            'graph_sha256':sha256(graph),'components_sha256':sha256(component_path),
            'seconds':time.monotonic()-started}
    args.report.with_suffix('.scc_verified.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)


if __name__=='__main__':
    main()
