"""Independent integer checks for the all-template period-eight obstruction."""
from itertools import combinations
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent


def rectangle(points):
    points=set(points)
    if len(points)!=4:return False
    for A,C in combinations(points,2):
        B,E=points-{A,C}
        if (A[0]+C[0],A[1]+C[1])!=(B[0]+E[0],B[1]+E[1]):continue
        if sum((A[i]-C[i])**2 for i in (0,1))==sum((B[i]-E[i])**2 for i in (0,1)):
            return True
    return False


def certificate(t,mask):
    h=38*t+1;q=19*t*(19*t+1);owner=8*(q-1)
    f=lambda x:h if mask>>(x%8-1)&1 else 1
    # All queries to f are at nonzero residues.
    A=f(t);B=f(3*t);C=f(4*t)
    extra={}
    if A!=f(5*t) or B!=f(7*t):
        if A!=f(5*t):r,p,z=t+1,t,37*t;kind='right_angle_1'
        else:r,p,z=5*t+1,3*t,55*t;kind='right_angle_2'
        W=(p+z,h+1-r)
        R={(0,r),(p,f(p)),(z,f(z)),W}
        sea=f(W[0]);extra[owner]={sea,W[1]}
        S={W,(W[0],sea),(owner,sea),(owner,W[1])}
        multiplicity=19*t+1
    elif B==C or A==C:
        horizontal=B==C
        color=B if horizontal else A
        r=4*t+1 if color==1 else h-4*t
        middle=2*t+1 if color==1 else h-2*t
        sign=1 if horizontal else -1
        R={(0,r),(sign*3*t,color),(-sign*t,middle),(sign*4*t,middle)}
        S={(-sign*t,color),(sign*4*t,color),(-sign*t,middle),(sign*4*t,middle)}
        multiplicity=19*t;kind='horizontal'
    else:
        r=34*t+1
        R={(0,r),(17*t,1),(4*t,36*t+1),(21*t,2*t+1)}
        S={(13*t,1),(12*t,h),(4*t,36*t+1),(21*t,2*t+1)}
        if A==h:
            R={(x,h+1-y) for x,y in R};S={(x,h+1-y) for x,y in S}
            r=h+1-r
        multiplicity=19*t;kind='mixed'
    extra[0]={r,1 if r%2==0 else 2}
    def black(point):
        x,y=point
        if x in extra:return y in extra[x]
        assert x%8,point
        return y==f(x)
    assert rectangle(R) and rectangle(S) and R!=S,(t,mask,kind)
    assert all(1<=y<=h for x,y in R|S)
    assert {P for P in R if not black(P)}=={P for P in S if not black(P)}
    local=R if kind.startswith('right_angle') else R|S
    left=max(0,-min(x for x,y in local));right=max(0,max(x for x,y in local))
    boundary_slots=(left+7)//8+(right+7)//8
    assert boundary_slots<multiplicity
    return kind


def main():
    counts={}
    for t in range(1,32,2):
        for mask in range(128):
            kind=certificate(t,mask);counts[kind]=counts.get(kind,0)+1
    classification_checks=0
    for h in range(11,200,4):
        rows=[(4,1,3*(h-4)),(4,3,h-4)] if h%8==3 else [(2,1,h-2),(10,3,3*(h-10))]
        for r,p,q in rows:
            assert p*q==(r-1)*(h-r)
            assert r%2==0 and (h+1-r)%2==0 and (p+q)%4==2
            assert (p+q+7)//8<(h+1)//2
            classification_checks+=1
    out={'status':'PASS','patterns':128,'odd_scales_checked':list(range(1,32,2)),
         'geometric_certificates':sum(counts.values()),'certificate_types':counts,
         'general_classification_checks':classification_checks}
    (HERE/'period_eight_obstruction_check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__':main()
