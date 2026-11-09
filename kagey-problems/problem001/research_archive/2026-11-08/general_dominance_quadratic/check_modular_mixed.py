"""Exact mixed-collision checks with three ramp points and one tail point.

Ramp y=x mod p for x<0; tail y=p-2 for x>=0. This enumerates the
three-ramp/one-tail case only, not every possible bridge obstruction.
"""
from math import isqrt
from pathlib import Path
import json
import time

HERE=Path(__file__).resolve().parent


def check_candidate(A,B,C,D,p,ramp_indices):
    pts=(A,B,C,D)
    if len(set(pts))!=4:
        return None
    U=(B[0]-A[0],B[1]-A[1])
    V=(D[0]-C[0],D[1]-C[1])
    if not U[0] or not U[1] or V==U or V==(-U[0],-U[1]):
        return None
    H=(A[0]+B[0]-C[0]-D[0],A[1]+B[1]-C[1]-D[1])
    if H==(0,0):
        return None
    assert sum(t*t for t in U)==sum(t*t for t in V)
    assert sum(x*y for x,y in zip(H,U))==0
    numerators=((C[0]+D[0]-U[0],C[1]+D[1]-U[1]),
                (C[0]+D[0]+U[0],C[1]+D[1]+U[1]))
    if any(x%2 or y%2 for x,y in numerators):
        return None
    whites=tuple((x//2,y//2) for x,y in numerators)
    if not all(0<=y<p for x,y in whites):
        return None
    tail_indices=[i for i in range(4) if i not in ramp_indices]
    shift=(max(pts[i][0] for i in ramp_indices)//p+1)*p
    if any(pts[i][0]<shift for i in tail_indices):
        return None
    shifted=tuple((x-shift,y) for x,y in pts)
    for x,y in shifted:
        assert y==(x%p if x<0 else p-2)
    return {'black_side':shifted[:2],'black_diagonal':shifted[2:],
            'white_pair':[(x-shift,y) for x,y in whites],
            'tail_indices':tail_indices}


def search(p,deadline):
    W=1+(p-1)**2//4
    tail=p-2
    tested=0
    for y1 in range(p):
        for y2 in range(p):
            dy=y2-y1
            first=dy%p or p
            for dx in range(first,W+1,p):
                P=(y1,y1)
                Q=(y1+dx,y2)
                norm=dx*dx+dy*dy
                for z in range(p):
                    delta=tail-z
                    square=norm-delta*delta
                    if square<=0:
                        continue
                    horizontal=isqrt(square)
                    if horizontal*horizontal!=square:
                        continue
                    if dy:
                        # P,Q are the side; C is ramp and D is tail.
                        numerator=(P[0]+Q[0]-horizontal)*dx+(P[1]+Q[1]-delta-2*z)*dy
                        denominator=2*dx
                        if numerator%denominator==0:
                            x=numerator//denominator
                            if x%p==z:
                                tested+=1
                                result=check_candidate(P,Q,(x,z),(x+horizontal,tail),p,{0,1,2})
                                if result:
                                    return {'p':p,'complete_one_tail_case':True,'counterexample':result,
                                            'integral_candidates_tested':tested}
                    if delta:
                        # P,Q are the diagonal; A is ramp and B is tail.
                        numerator=(P[0]+Q[0]-horizontal)*horizontal+(P[1]+Q[1]-delta-2*z)*delta
                        denominator=2*horizontal
                        if numerator%denominator==0:
                            x=numerator//denominator
                            if x%p==z:
                                tested+=1
                                result=check_candidate((x,z),(x+horizontal,tail),P,Q,p,{0,2,3})
                                if result:
                                    return {'p':p,'complete_one_tail_case':True,'counterexample':result,
                                            'integral_candidates_tested':tested}
                if time.monotonic()>deadline:
                    return {'p':p,'complete_one_tail_case':False,'reason':'time cap',
                            'integral_candidates_tested':tested}
    return {'p':p,'complete_one_tail_case':True,'counterexample':None,
            'integral_candidates_tested':tested}


def main():
    started=time.monotonic()
    deadline=started+100
    results=[]
    for p in (3,5,11,13,19,29,37,43):
        assert pow(2,(p-1)//2,p)==p-1
        result=search(p,deadline)
        results.append(result)
        print(json.dumps(result),flush=True)
        if result.get('counterexample') or not result['complete_one_tail_case']:
            break
    out={'scope':'mixed collisions with exactly one tail black point',
         'results':results,'elapsed_seconds':time.monotonic()-started}
    (HERE/'modular_mixed_one_tail_checks.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':
    main()
