"""Exact finite checks for the general dominance comparison lemmas."""
from itertools import combinations,combinations_with_replacement
from math import isqrt
from pathlib import Path
import json
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'counting_followup'))
from dominance_compatibility import compatibility,allowed


def vertical_pairs(h,word):
    out=set()
    for x,z in combinations(range(len(word)),2):
        a,b=word[x],word[z]
        square=(z-x)**2+(b-a)**2
        length=isqrt(square)
        if length*length!=square or (x+z)%2 or (a+b+length)%2:
            continue
        lo=(a+b-length)//2
        hi=(a+b+length)//2
        if 1<=lo<hi<=h:
            out.add((lo,hi))
    return out


def partitions(h):
    for block in combinations(range(1,h+1),h//2):
        if h%2==0 and 1 not in block:
            continue
        yield set(block)


def constants(h,block):
    return [r for r in range(1,h+1)
            if all(((r-d) in block)==((r+d) in block)
                   for d in range(1,min(r-1,h-r)+1))]


def main():
    started=time.monotonic()
    mono=[]
    for h in range(3,9):
        n=5
        L=2*(1+(h-1)**2//4)
        count=0
        for word in combinations_with_replacement(range(1,h+1),n):
            expected=vertical_pairs(h,word)
            assert compatibility(h,word)==expected,(h,word)
            padded=(1,)*L+word+(h,)*L
            assert vertical_pairs(h,padded)==expected,(h,word,'vertical-padding')
            assert compatibility(h,padded)==expected,(h,word,'geometric-padding')
            count+=1
        mono.append({'height':h,'word_length':n,'all_monotone_words':count,'padding_each_side':L})
    fixed=[]
    for h in range(3,15):
        parity=set(range(1,h+1,2))
        maxima=[]
        defect_counts=[]
        for block in partitions(h):
            if block==parity or set(range(1,h+1))-block==parity:
                continue
            good=constants(h,block)
            assert len(good)<=h//2+1
            defect=sum((a-b)%2==0 and ((a in block)!=(b in block))
                       for a,b in combinations(range(1,h+1),2))
            assert defect>=(h//2 if h%2 else h-2)
            maxima.append(len(good))
            defect_counts.append(defect)
        fixed.append({'height':h,'nonparity_partitions':len(maxima),
                      'maximum_constant_seas':max(maxima),
                      'minimum_same_parity_cross_pairs':min(defect_counts)})
    word=tuple(range(1,15))+(2,14,2,14,6)
    parity=set(range(1,15,2))
    assert allowed(compatibility(14,word),parity)
    assert not allowed(compatibility(14,(1,1,1)+word),parity)
    A,B,C,D=(1,1),(21,6),(2,1),(18,14)
    U=(B[0]-A[0],B[1]-A[1]);V=(D[0]-C[0],D[1]-C[1])
    H=(A[0]+B[0]-C[0]-D[0],A[1]+B[1]-C[1]-D[1])
    assert sum(x*x for x in U)==sum(x*x for x in V)==425
    assert sum(x*y for x,y in zip(H,U))==0
    result={'status':'passed','monotone_checks':mono,'fixed_point_checks':fixed,
            'staircase_counterexample':{'height':14,'word':word,'finite_valid':True,
                                        'three_boundary_prefix_valid':False},
            'elapsed_seconds':time.monotonic()-started}
    (HERE/'dominance_comparison_checks.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result),flush=True)


if __name__=='__main__':
    main()
