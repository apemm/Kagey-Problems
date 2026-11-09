"""Independent fixed-core geometry through complete rectangle-presentation fibers."""
from itertools import combinations
from presentation_fiber_cnf import encode as fiber_encode

_CACHE={}


def encode(w,record,rects,flags,known_bounds=None):
    from pysat.card import CardEnc,EncType
    n=7*w
    if w not in _CACHE:_CACHE[w]=fiber_encode(rects,n,no_hidden=True)
    geometry,top,geometry_info=_CACHE[w]
    clauses=list(geometry);core=record['masks'];empty=record['empty_columns']
    types=([0] if empty else [])+[1<<r for r in range(7)]+core
    first=7+empty;ntypes=len(types);offset=top
    tv=lambda c,j:offset+c*ntypes+j+1
    top+=w*ntypes
    for c in range(w):
        clauses.append([tv(c,j) for j in range(ntypes)])
        clauses.extend([-tv(c,j),-tv(c,k)] for j,k in combinations(range(ntypes),2))
        for r in range(7):
            holders=[tv(c,j) for j,T in enumerate(types) if T>>r&1]
            point=r*w+c+1
            clauses.append([-point]+holders)
            clauses.extend([-v,point] for v in holders)
    for j in list(range(first,ntypes))+([0] if empty else []):
        clauses.append([tv(c,j) for c in range(w)])
        clauses.extend([-tv(c,j),-tv(d,j)] for c,d in combinations(range(w),2))
    clauses.append([tv(c,first) for c in range((w+1)//2)])
    for length,bound in (known_bounds or {}).items():
        if length>=w:continue
        for left in range(w-length+1):
            variables=[r*w+c+1 for r in range(7) for c in range(left,left+length)]
            extra=CardEnc.atmost(variables,bound,top_id=top,encoding=EncType.totalizer)
            clauses+=extra.clauses;top=extra.nv
    return clauses,{**geometry_info,'variables':top,'clauses':len(clauses),
                    'geometry_clauses':len(geometry),
                    'geometry':'complete rectangle presentation fibers'}
