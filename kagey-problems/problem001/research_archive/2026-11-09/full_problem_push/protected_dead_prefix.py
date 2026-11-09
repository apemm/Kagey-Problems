"""Extract a short all-odd prefix with no all-odd next letter."""
from pathlib import Path
import importlib.util
import json
import struct
import sys
import numpy as np

HERE=Path(__file__).resolve().parent
graph=HERE/'sea_packed_h7_odd.bin'
with graph.open('rb') as source:
    magic,k,n=struct.unpack('<iii',source.read(12))
assert magic==0x53454731 and k==4
edges=np.memmap(graph,mode='r',dtype='<i4',offset=12,shape=(n,k))
dead=np.flatnonzero(np.all(edges<0,axis=1))
assert len(dead)
target=int(dead[0])
state=target
reverse=[]
while state:
    found=False
    for start in range(0,state,100000):
        block=np.asarray(edges[start:min(state,start+100000)])
        where=np.argwhere(block==state)
        if len(where):
            offset,letter=map(int,where[0])
            reverse.append(2*letter+1)
            state=start+offset
            found=True
            break
    assert found
word=tuple(reversed(reverse))
state=0
for r in word:
    state=int(edges[state,(r-1)//2])
    assert state>=0
assert state==target

sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles,collision
pad=20
width=len(word)+1+2*pad
rects=rectangles(7,width)
def mask(w):
    return sum(1<<((r-1)*width+pad+x) for x,r in enumerate(w))
assert collision(rects,mask(word)) is None
def points(R):
    return [[p%width-pad,p//width+1] for p in range(7*width) if R>>p&1]
certificates=[]
for r in (1,3,5,7):
    hit=collision(rects,mask(word+(r,)))
    assert hit is not None
    first,second=hit
    visible=first & ~mask(word+(r,))
    assert visible==second & ~mask(word+(r,))
    certificates.append(dict(appended_row=r,rectangles=[points(first),points(second)],
                             common_white_presentation=points(visible)))

full=HERE/'sea_packed_h7.bin'
with full.open('rb') as source:
    magic,h,nfull=struct.unpack('<iii',source.read(12))
full_edges=np.memmap(full,mode='r',dtype='<i4',offset=12,shape=(nfull,h))
components=np.memmap(str(full)+'.components',mode='r',dtype='<i4',offset=4,shape=(nfull,))
state=0
for r in word:
    state=int(full_edges[state,r-1])
    assert state>=0
result=dict(status='PASS',height=7,word=list(word),protected_dead_state=target,
            zero_outdegree_protected_states=len(dead),full_sea_state=state,
            full_sea_component=int(components[state]),
            full_next_rows=[r+1 for r,j in enumerate(full_edges[state]) if j>=0],
            padded_width=width,rectangles_checked=len(rects),
            next_letter_collisions=certificates)
(HERE/'protected_dead_prefix_h7.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
