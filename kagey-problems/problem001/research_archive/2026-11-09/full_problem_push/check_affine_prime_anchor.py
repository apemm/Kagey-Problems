"""Exact search for a two-pin mixed obstruction to checkerboard prime buffers."""
from math import isqrt
import json
from pathlib import Path

def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))

def divisors(n):
    ans=[]
    for d in range(1,isqrt(n)+1):
        if n%d==0:
            ans.append(d)
            if d*d!=n: ans.append(n//d)
    return ans

def find(limit=200, accept=None):
    pool=[a+2*p for p in range(3,limit+1,4) if prime(p) for a in (1,2)]
    for a in (1,2):
        for c_row in (1,2):
            for b in pool:
                y=b-a
                for d in pool:
                    v=d-c_row
                    hy=a+b-c_row-d
                    if hy==0:
                        continue
                    for x in divisors(abs(y*hy)):
                        if (x-y)%2:
                            continue
                        norm=x*x+y*y
                        z2=norm-v*v
                        if z2<=0:
                            continue
                        z=isqrt(z2)
                        if z*z!=z2 or (z-v)%2 or (z,v)==(x,y):
                            continue
                        c2=x-z+y*hy//x
                        if c2%2:
                            continue
                        c=c2//2
                        if (c-(c_row-a))%2:
                            continue
                        if x==c+z:
                            continue
                        lo=max(0,c)+1
                        hi=min(x,c+z)
                        cut=lo+((a-1-lo)%2)
                        if cut>hi:
                            continue
                        wx2=2*c+z-x
                        wy2=c_row+d-y
                        if wx2%2 or wy2%2:
                            continue
                        wx,wy=wx2//2,wy2//2
                        if wy<1:
                            continue
                        W=(wx-cut,wy); Z=(wx+x-cut,wy+y)
                        A=(-cut,a); B=(x-cut,b)
                        C=(c-cut,c_row); D=(c+z-cut,d)
                        pts=(A,B,C,D)
                        assert all((py-px-1)%2==0 for px,py in pts)
                        assert all(px<0 and py==1+(px%2) for px,py in (A,C))
                        assert all(px>=0 and prime((py-(1+px%2))//2)
                                   and ((py-(1+px%2))//2)%4==3 for px,py in (B,D))
                        assert len({A,B,C,D})==4
                        assert len({C,D,W,Z})==4 and len({A,B,W,Z})==4
                        assert (B[0]-A[0])*(W[0]-A[0])+(B[1]-A[1])*(W[1]-A[1])==0
                        assert A[0]+Z[0]==B[0]+W[0] and A[1]+Z[1]==B[1]+W[1]
                        assert C[0]+D[0]==W[0]+Z[0] and C[1]+D[1]==W[1]+Z[1]
                        assert (D[0]-C[0])**2+(D[1]-C[1])**2 == norm
                        result=dict(A=A,B=B,C=C,D=D,W=W,Z=Z,
                                    height=max(p[1] for p in (*pts,W,Z)),
                                    norm=norm,cut=cut)
                        if accept is None or accept(result):
                            return result
    return None

if __name__=="__main__":
    result=find()
    print(json.dumps(result,indent=2))
    Path(__file__).with_suffix(".json").write_text(json.dumps(result,indent=2)+"\n")

