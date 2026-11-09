"""Check the finite five-chromatic graph inside an actual scaffold block."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
source = HERE/'odd_graph_five_chromatic.json'
data = json.loads(source.read_text())
vertices = data['vertices']
edges = data['edges_with_base_and_root']
assert all(u > 0 and u % 2 for u in vertices)
A = max((z-base)//2 for u,v,base,z in edges)
C = max(max(vertices), max((z+base)//2 for u,v,base,z in edges))
R = max(A,C,1)
h = 4*R
B = 2*R
# Primality is immaterial to this embedding; the block-separation inequality
# is the only condition used here.
p = 10*h+1
column = {u:4*((B+u-1)//2+p*(B-2)//2) for u in vertices}
for u,v,base,z in edges:
    assert base in (u,v)
    other = v if base == u else u
    assert z*z == base*base+4*(other-base)**2
    assert z > base and z % 2 == 1
    x1,x2 = column[base],column[other]
    assert (x2-x1)**2+base**2 == z*z
    low,high = B+(base-z)//2,B+(base+z)//2
    assert 1 <= low < high <= h and (high-low) % 2 == 1
    assert (x1+x2) % 2 == 0
    mid = (x1+x2)//2
    assert min(x1,x2) < mid < max(x1,x2)
    odd,even = (low,high) if low % 2 else (high,low)
    owner = 4*((odd-1)//2+p*(even-2)//2)
    assert even != B and owner != mid
    assert 1 <= B+base <= h and 1 <= B+other <= h
result = dict(status='PASS',vertices=len(vertices),edges=len(edges),
              required_colors=5,source=source.name,
              source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
              A=A,C=C,height=h,even_block_row=B,
              block_separation_parameter=p,
              checks='All integer diagonals, strip bounds, parity pairs, and distinct axis owners')
(HERE/'in_strip_p_embedding_check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
