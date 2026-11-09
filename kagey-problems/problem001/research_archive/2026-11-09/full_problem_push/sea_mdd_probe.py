"""Exact multi-valued decision-diagram compression of pending sea constraints.

This is a bounded prototype. A node denotes a Boolean function of future
column letters, with reduced ordered h-way decision nodes. False functions
have no infinite continuation and are omitted from the recurrent language.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import struct
import time

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('sea_export', HERE/'export_sea_residuals.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class MDD:
    def __init__(self,h):
        self.h=h
        self.nodes=[(10**9,),(10**9,)]
        self.unique={}
        self.products={}
        self.shifts={0:0,1:1}

    def make(self,var,children):
        children=tuple(children)
        if all(c==children[0] for c in children):
            return children[0]
        key=(var,)+children
        old=self.unique.get(key)
        if old is not None:
            return old
        value=len(self.nodes)
        self.unique[key]=value
        self.nodes.append(key)
        return value

    def product(self,a,b):
        if a==0 or b==0:
            return 0
        if a==1 or a==b:
            return b
        if b==1:
            return a
        if a>b:
            a,b=b,a
        key=(a,b)
        old=self.products.get(key)
        if old is not None:
            return old
        aa,bb=self.nodes[a],self.nodes[b]
        var=min(aa[0],bb[0])
        children=[self.product(aa[r+1] if aa[0]==var else a,
                               bb[r+1] if bb[0]==var else b)
                  for r in range(self.h)]
        value=self.make(var,children)
        self.products[key]=value
        return value

    def shift(self,a):
        old=self.shifts.get(a)
        if old is not None:
            return old
        node=self.nodes[a]
        assert node[0]>0
        value=self.make(node[0]-1,[self.shift(c) for c in node[1:]])
        self.shifts[a]=value
        return value

    def forbid(self,pattern):
        node=0
        for x,r in reversed(pattern):
            children=[1]*self.h
            children[r-1]=node
            node=self.make(x,children)
        return node

    def advance(self,node,r):
        if node>1 and self.nodes[node][0]==0:
            node=self.nodes[node][r]
        return self.shift(node)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('height',type=int)
    parser.add_argument('--seconds',type=float,default=120)
    parser.add_argument('--node-cap',type=int,default=1000000)
    parser.add_argument('--state-cap',type=int,default=1000000)
    args=parser.parse_args()
    start=time.monotonic()
    h=args.height
    patterns,stats=module.sea.forbidden_patterns(h,start+300)
    m=MDD(h)
    starts=[1]*(h+1)
    for p in patterns:
        first=p[0][1]
        tail=tuple((x-1,r) for x,r in p[1:])
        starts[first]=m.product(starts[first],m.forbid(tail))
    states=[1]
    index={1:0}
    transitions=[]
    cursor=0
    while cursor<len(states):
        row=[]
        for r in range(1,h+1):
            target=m.product(m.advance(states[cursor],r),starts[r])
            if target==0:
                row.append(-1)
                continue
            if target not in index:
                index[target]=len(states)
                states.append(target)
            row.append(index[target])
        transitions.append(row)
        cursor+=1
        if cursor%10000==0:
            print(json.dumps(dict(processed=cursor,states=len(states),nodes=len(m.nodes),
                                  products=len(m.products),seconds=time.monotonic()-start)),flush=True)
        if len(m.nodes)>args.node_cap or len(states)>args.state_cap or time.monotonic()-start>args.seconds:
            break
    complete=cursor==len(states)
    result=dict(height=h,complete=complete,processed=cursor,states=len(states),
                nodes=len(m.nodes),products=len(m.products),geometry=stats,
                seconds=time.monotonic()-start)
    stem=HERE/f'sea_mdd_h{h}'
    stem.with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    if complete:
        with stem.with_suffix('.bin').open('wb') as sink:
            sink.write(struct.pack('<iii',0x53454731,h,len(states)))
            for row in transitions:
                sink.write(struct.pack('<'+'i'*h,*row))
    print(json.dumps(result),flush=True)


if __name__=='__main__':
    main()
