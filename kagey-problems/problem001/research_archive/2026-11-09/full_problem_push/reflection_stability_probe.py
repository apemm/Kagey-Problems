"""Exact finite tests for possible approximate-reflection stability inequalities."""
from itertools import combinations
from fractions import Fraction
from pathlib import Path
import json
import sys
import time

HERE=Path(__file__).resolve().parent


def stats(h,A):
    reverse=int(f'{A:0{h}b}'[::-1],2)
    V=0;bits=A
    while bits:
        bit=bits&-bits;bits-=bit;a=bit.bit_length()-1
        radius=min(a,h-1-a)
        V+=(((reverse>>(h-a))^(A>>(a+1)))&((1<<radius)-1)).bit_count()
    adjacent=(A&(A>>1)).bit_count()
    even=sum(bool(A>>a&1) for a in range(1,h,2))
    odd=A.bit_count()-even
    return V,adjacent,even*odd


def main():
    maximum=int(sys.argv[1]) if len(sys.argv)>1 else 20
    begun=time.monotonic();out=[]
    for h in range(8,maximum+1):
        best_p=None;best_mix=None;count=0
        full=(1<<h)-1
        for rows in combinations(range(h),h//2):
            A=sum(1<<a for a in rows)
            for mask in ((A,full^A) if h%2 else (A,)):
                V,p,mix=stats(h,mask);count+=1
                word=''.join('1' if mask>>a&1 else '0' for a in range(h))
                if p and (best_p is None or Fraction(V,p*p)<best_p[0]):
                    best_p=(Fraction(V,p*p),V,p,word)
                if mix and (best_mix is None or Fraction(V,mix)<best_mix[0]):
                    best_mix=(Fraction(V,mix),V,mix,word)
        def item(best):
            ratio,V,den,word=best
            return {'ratio':str(ratio),'V':V,'parameter':den,'word':word}
        record={'height':h,'balanced_blocks':count,'minimum_V_over_p_squared':item(best_p),
                'minimum_V_over_even_times_odd':item(best_mix)}
        out.append(record);print(json.dumps(record),flush=True)
    result={'scope':'finite evidence only','records':out,'seconds':time.monotonic()-begun}
    (HERE/'reflection_stability_probe.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
