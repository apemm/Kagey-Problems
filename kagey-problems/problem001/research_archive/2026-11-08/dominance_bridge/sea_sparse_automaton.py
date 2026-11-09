"""Exact sparse-pattern automaton for the parity sea shift.

No full-word window enumeration. A state is an antichain of live residual
positive forbidden patterns. Normalizing their black support can prune finite
boundary words that have no bi-infinite extension; the sea shift and all its
recurrent components are unchanged. Geometry and transitions use integer arithmetic.
Optional floating-point power iteration only proposes an integer vector;
reported Collatz bounds are then computed exactly from that vector.
"""
from __future__ import annotations
import argparse
from array import array
from collections import Counter
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path
import sys
import time


def resident_bytes():
    if sys.platform!='win32':
        return 0
    import ctypes
    from ctypes import wintypes
    class Counters(ctypes.Structure):
        _fields_=[('cb',wintypes.DWORD),('faults',wintypes.DWORD)]+[
            (name,ctypes.c_size_t) for name in ('peak_working_set','working_set',
            'peak_paged','paged','peak_nonpaged','nonpaged','pagefile','peak_pagefile')]
    counters=Counters()
    counters.cb=ctypes.sizeof(counters)
    current=ctypes.windll.kernel32.GetCurrentProcess
    current.restype=wintypes.HANDLE
    memory=ctypes.windll.psapi.GetProcessMemoryInfo
    memory.argtypes=[wintypes.HANDLE,ctypes.POINTER(Counters),wintypes.DWORD]
    memory.restype=wintypes.BOOL
    process=current()
    ok=memory(process,ctypes.byref(counters),counters.cb)
    return counters.working_set if ok else 0


def normalize(cells):
    bycol={}
    for x,r in cells:
        if x in bycol and bycol[x]!=r:
            return None
        bycol[x]=r
    if not bycol:
        return None
    x0=min(bycol)
    return tuple(sorted((x-x0,r) for x,r in bycol.items()))


def tilted_shapes(h):
    out=set()
    for b in range(1,h):
        for d in range(1,h-b):
            for a in range(1,b*d+1):
                if b*d%a:
                    continue
                c=b*d//a
                for r in range(b+1,h-d+1):
                    out.add(tuple(sorted(((0,r),(a,r-b),(c,r+d),(a+c,r-b+d)))))
    return sorted(out)


def forbidden_patterns(h, deadline, part=None):
    part=set(range(1,h+1,2)) if part is None else set(part)
    separated=lambda r,s: (r in part)!=(s in part)
    shapes=tilted_shapes(h)
    patterns=set()
    def insert(cells):
        p=normalize(cells)
        if p is not None:
            patterns.add(p)
    for sh in shapes:
        insert(sh)
        for x,r in sh:
            others=[c for c in sh if c!=(x,r)]
            for s in range(1,h+1):
                if separated(r,s):
                    insert(others+[(x,s)])
        for whites in combinations(sh,2):
            others=[c for c in sh if c not in whites]
            (x,r),(z,s)=whites
            if x==z:
                if separated(r,s):
                    insert(others)
            elif r==s:
                for t in range(1,h+1):
                    if t!=r:
                        insert(others+[(x,t),(z,t)])
            else:
                insert(others+[(x,s),(z,r)])
    # Two tilted rectangles sharing a corner. Their symmetric difference must
    # not be all black. Patterns with repeated columns are impossible in a sea.
    anchored=[set() for _ in range(h+1)]
    for sh in shapes:
        for x,r in sh:
            anchored[r].add(frozenset((z-x,s) for z,s in sh))
    pair_count=0
    for group in anchored:
        for a,b in combinations(group,2):
            insert(a^b)
            pair_count+=1
            if pair_count%10000==0 and time.monotonic()>deadline:
                raise TimeoutError('geometry generation time cap')
    raw=len(patterns)
    # Remove every pattern containing a translated smaller forbidden pattern.
    minimal=[]
    kept=set()
    for p in sorted(patterns,key=lambda p:(len(p),p)):
        redundant=False
        for size in range(1,len(p)):
            if any(normalize(sub) in kept for sub in combinations(p,size)):
                redundant=True
                break
        if not redundant:
            kept.add(p)
            minimal.append(p)
    return minimal,{'tilted_shapes':len(shapes),'anchored_rectangle_pairs':pair_count,
                    'raw_patterns':raw,'minimal_patterns':len(minimal),
                    'patterns_by_size':dict(Counter(map(len,minimal))),
                    'maximum_pattern_span':max(p[-1][0] for p in minimal)}


def build_residuals(patterns,h):
    universe=set()
    for p in patterns:
        for age in range(1,p[-1][0]+1):
            universe.add(tuple((x-age,r) for x,r in p if x>=age))
    # Consecutive leading-wildcard states of one normalized residual form a
    # consecutive bit run. Advancing all of them is one right shift.
    residuals=sorted(universe,key=lambda p:(len(p),tuple((x-p[0][0],r) for x,r in p),p[0][0]))
    index={p:i for i,p in enumerate(residuals)}
    supersets=[0]*len(residuals)
    subsets=[0]*len(residuals)
    for i,p in enumerate(residuals):
        for size in range(1,len(p)+1):
            for sub in combinations(p,size):
                j=index.get(sub)
                if j is not None:
                    supersets[j] |= 1<<i
                    subsets[i] |= 1<<j
    successor=[0]*len(residuals)
    valid=[0]*(h+1)
    reject=[0]*(h+1)
    starts=[0]*(h+1)
    wildcard=0
    for i,p in enumerate(residuals):
        bit=1<<i
        if p[0][0]==0 and len(p)==1:
            reject[p[0][1]] |= bit
            continue
        tail=tuple((x-1,r) for x,r in p if x>0)
        successor[i]=1<<index[tail]
        if p[0][0]>0:
            assert index[tail]==i-1
            wildcard |= bit
        else:
            valid[p[0][1]] |= bit
    for p in patterns:
        starts[p[0][1]] |= 1<<index[tuple((x-1,r) for x,r in p[1:])]
    def canonical(bits):
        out=0
        while bits:
            bit=bits&-bits
            i=bit.bit_length()-1
            out |= bit
            bits &= ~supersets[i]
        return out
    starts=[canonical(x) for x in starts]
    def transition(state,letter):
        if state&reject[letter]:
            return None
        bits=state&valid[letter]
        addition=starts[letter]
        while bits:
            bit=bits&-bits
            bits-=bit
            addition |= successor[bit.bit_length()-1]
        # The shifted wildcard part is already an antichain. Only newly
        # activated or just-matched residuals need to be merged into it.
        out=(state&wildcard)>>1
        while addition:
            bit=addition&-addition
            i=bit.bit_length()-1
            addition-=bit
            if not out&subsets[i]:
                out=(out&~supersets[i])|bit
                addition &= ~supersets[i]
        return out
    return transition,len(residuals)


def build_graph(transition,h,deadline,state_cap,memory_mb):
    states=[0]
    index={0:0}
    trans=array('i')
    keybytes=sys.getsizeof(0)
    cursor=0
    last_progress=0
    while cursor<len(states):
        for letter in range(1,h+1):
            nxt=transition(states[cursor],letter)
            if nxt is None:
                trans.append(-1)
                continue
            j=index.get(nxt)
            if j is None:
                j=len(states)
                index[nxt]=j
                states.append(nxt)
                keybytes+=sys.getsizeof(nxt)
            trans.append(j)
        cursor+=1
        if cursor%1000==0:
            estimate=max(resident_bytes(),keybytes+sys.getsizeof(states)+sys.getsizeof(index)+sys.getsizeof(trans)+len(index)*28)
            if cursor-last_progress>=10000:
                print(json.dumps({'phase':'bfs','processed':cursor,'discovered':len(states),
                                  'estimated_mb':round(estimate/2**20,1)}),flush=True)
                last_progress=cursor
            reason=('state cap' if len(states)>state_cap else
                    'memory cap' if estimate>memory_mb*2**20 else
                    'time cap' if time.monotonic()>deadline else None)
            if reason:
                return states,trans,False,{'stop_reason':reason,'processed_states':cursor,
                                         'estimated_mb':estimate/2**20}
    return states,trans,True,{'processed_states':cursor}


def scc(trans,h):
    n=len(trans)//h
    visited=bytearray(n)
    order=array('i')
    for start in range(n):
        if visited[start]:
            continue
        visited[start]=1
        stack=[(start,0)]
        while stack:
            v,k=stack[-1]
            if k==h:
                order.append(v)
                stack.pop()
                continue
            stack[-1]=(v,k+1)
            w=trans[v*h+k]
            if w>=0 and not visited[w]:
                visited[w]=1
                stack.append((w,0))
    counts=array('i',[0])*n
    for w in trans:
        if w>=0:
            counts[w]+=1
    offsets=array('i',[0])
    for count in counts:
        offsets.append(offsets[-1]+count)
    reverse=array('i',[0])*offsets[-1]
    positions=array('i',offsets[:-1])
    for v in range(n):
        for k in range(h):
            w=trans[v*h+k]
            if w>=0:
                reverse[positions[w]]=v
                positions[w]+=1
    component=array('i',[-1])*n
    sizes=[]
    for start in reversed(order):
        if component[start]>=0:
            continue
        cid=len(sizes)
        component[start]=cid
        size=0
        stack=[start]
        while stack:
            v=stack.pop()
            size+=1
            for j in range(offsets[v],offsets[v+1]):
                w=reverse[j]
                if component[w]<0:
                    component[w]=cid
                    stack.append(w)
        sizes.append(size)
    cyclic=set(i for i,size in enumerate(sizes) if size>1)
    for v in range(n):
        if any(trans[v*h+k]==v for k in range(h)):
            cyclic.add(component[v])
    return component,sizes,cyclic


def exact_spectral_bounds(trans,h,component,cid,iterations=250):
    import numpy as np
    members=[i for i,c in enumerate(component) if c==cid]
    index={v:i for i,v in enumerate(members)}
    rows=np.full((len(members),h),len(members),dtype=np.int64)
    for i,v in enumerate(members):
        for k in range(h):
            rows[i,k]=index.get(trans[v*h+k],len(members))
    vector=np.ones(len(members)+1)
    vector[-1]=0
    for _ in range(iterations):
        nxt=vector[:-1]+vector[rows].sum(axis=1)
        vector[:-1]=nxt/nxt.max()
    weights=[max(1,int(float(x)*10**13)) for x in vector[:-1]]
    weights.append(0)
    lo=None
    hi=None
    for i,row in enumerate(rows):
        numerator=sum(weights[int(j)] for j in row)
        ratio=Fraction(numerator,weights[i])
        lo=ratio if lo is None or ratio<lo else lo
        hi=ratio if hi is None or ratio>hi else hi
    return {'lower_fraction':str(lo),'upper_fraction':str(hi),
            'lower_float':float(lo),'upper_float':float(hi),
            'integer_vector_scale':10**13,'proposal_iterations':iterations}


def main():
    p=argparse.ArgumentParser()
    p.add_argument('height',type=int)
    p.add_argument('--seconds',type=float,default=150)
    p.add_argument('--states',type=int,default=300000)
    p.add_argument('--memory-mb',type=int,default=768)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--no-spectrum',action='store_true')
    args=p.parse_args()
    started=time.monotonic()
    deadline=started+args.seconds
    result={'height':args.height,'time_cap_seconds':args.seconds,'state_cap':args.states,
            'memory_cap_mb':args.memory_mb,'complete':False}
    try:
        patterns,stats=forbidden_patterns(args.height,deadline)
        result.update(stats)
        print(json.dumps({'phase':'geometry',**stats}),flush=True)
        transition,nres=build_residuals(patterns,args.height)
        result['residual_universe']=nres
        print(json.dumps({'phase':'residuals','count':nres}),flush=True)
        if resident_bytes()>args.memory_mb*2**20:
            raise TimeoutError('memory cap after residual generation')
        states,trans,complete,bfs=build_graph(transition,args.height,deadline,args.states,args.memory_mb)
        result.update(bfs)
        result['states']=len(states)
        result['complete']=complete
        if complete:
            result['edges']=sum(x>=0 for x in trans)
            comp,sizes,cyclic=scc(trans,args.height)
            result['scc_size_histogram']=dict(Counter(sizes))
            result['cyclic_components']=[]
            constant_states=[]
            for r in range(1,args.height+1):
                v=0
                for _ in range(2*(1+(args.height-1)**2//4)+1):
                    v=trans[v*args.height+r-1]
                    assert v>=0
                assert trans[v*args.height+r-1]==v
                constant_states.append(v)
            result['constant_states']=constant_states
            result['constant_components']=[comp[v] for v in constant_states]
            for cid in sorted(cyclic,key=lambda c:-sizes[c]):
                entry={'id':cid,'size':sizes[cid],
                       'constant_rows':[r+1 for r,v in enumerate(constant_states) if comp[v]==cid]}
                if not args.no_spectrum:
                    entry['rho_bounds']=exact_spectral_bounds(trans,args.height,comp,cid)
                result['cyclic_components'].append(entry)
        result['elapsed_seconds']=time.monotonic()-started
    except TimeoutError as exc:
        result['stop_reason']=str(exc)
        result['elapsed_seconds']=time.monotonic()-started
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result),flush=True)


if __name__=='__main__':
    main()
