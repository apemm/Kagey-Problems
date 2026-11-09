"""Exact certificates for the canonical separable CRT P obstruction.

Membership is computed from inverse CRT residues. No full label family is
materialized. Standard library only.
"""
from pathlib import Path
from math import gcd, isqrt
import hashlib
import json
import random
import struct

def prime_after(n):
    n += 1 if n % 2 == 0 else 2
    while True:
        if all(n % d for d in range(3, isqrt(n)+1, 2)):
            return n
        n += 2

def power_two_at_least(n):
    return 1 << (n-1).bit_length()

def make_map(n, N, kind, seed):
    rng=random.Random(seed)
    if kind=="identity":
        out=list(range(n))
    elif kind=="random_injection":
        out=rng.sample(range(N), n)
    elif kind=="dyadic_isometry":
        bits=N.bit_length()-1
        flips=[[rng.randrange(2) for _ in range(1<<k)] for k in range(bits)]
        out=[]
        for j in range(n):
            y=0
            for k in range(bits):
                bit=((j>>k)&1)^flips[k][j&((1<<k)-1)]
                y |= bit<<k
            out.append(y)
    else:
        raise ValueError(kind)
    assert len(set(out))==n
    digest=hashlib.sha256(b"".join(struct.pack("<I", v) for v in out)).hexdigest()
    return out,digest

def solve(h, kind, seed):
    no=(h+1)//2
    ne=h//2
    p=prime_after(10*h)
    N=power_two_at_least(ne)
    F,digest=make_map(ne,N,kind,seed)
    invF={v:j for j,v in enumerate(F)}
    pinv=pow(p,-1,N)
    D=isqrt(h)//10

    central=[j for j in range(ne) if h <= 3*(2*j+2) <= 2*h]
    candidates=[]
    for parity in (0,1):
        group=sorted((F[j],j) for j in central if F[j]%2==parity)
        for (f1,j1),(f2,j2) in zip(group,group[1:]):
            d=f2-f1
            if 0<d<=D:
                candidates.append((d,f1,f2,j1,j2))
    assert candidates, (h,kind,D)
    d,f1,f2,j1,j2=max(candidates)
    assert d%2==0
    b1,b2=2*j1+2,2*j2+2
    v,L=4*d*d-1,4*d*d+1

    def center(a,b):
        assert a%2==1 and b%2==0 and 1<=a<=h and 1<=b<=h
        i,j=(a-1)//2,(b-2)//2
        z=i+p*((F[j]-i)*pinv%N)
        assert 0<=z<p*N and z%p==i and z%N==F[j]
        return z

    results=[]
    for residue in (1,3):
        a=next(a for a in (b2-v,b2+v) if a%4==residue)
        a2=a+2*d
        assert 1<=a<=h and 1<=a2<=h
        z1,z2=center(a,b1),center(a2,b2)
        assert z2-z1==d
        x1,x2=4*z1,4*z2
        mid=(x1+x2)//2
        low,high=(a+b2-L)//2,(a+b2+L)//2
        assert (a+b2-L)%2==0 and 1<=low<high<=h
        odd=low if low%2 else high
        even=high if low%2 else low
        assert odd%4==residue
        zo=center(odd,even)
        xo=4*zo
        assert xo not in (x1,x2,mid)
        A,B=(x1,a),(x2,b2)
        U,V=(mid,low),(mid,high)
        R=tuple(sorted((A,B,U,V)))
        T=tuple(sorted((U,V,(xo,low),(xo,high))))
        assert (x2-x1)**2+(b2-a)**2==(high-low)**2
        assert x1+x2==2*mid and a+b2==low+high

        def is_black(point):
            x,y=point
            if x%4: return False
            z=x//4
            if not 0<=z<p*N: return False
            i=z%p
            j=invF.get(z%N)
            if i>=no or j is None: return False
            aa=2*i+1
            if aa%4!=residue: return False
            return y in (aa,2*j+2)

        WR=tuple(P for P in R if not is_black(P))
        WT=tuple(P for P in T if not is_black(P))
        assert R!=T and WR==WT and WR
        assert not is_black((mid,odd))
        sym=set(R)^set(T)
        assert len(sym)==4 and all(is_black(P) for P in sym)
        results.append({
            "retained_odd_residue_mod4":residue,
            "labels":[[a,b1],[a2,b2],[odd,even]],
            "crt_centers_z":[z1,z2,zo],
            "tilted_rectangle":R,
            "axis_rectangle":T,
            "common_white_presentation":WR,
            "symmetric_difference_black":sorted(sym),
        })
    return {
        "height":h,"prime":p,"modulus":N,"map":kind,"seed":seed,
        "map_sha256_le32":digest,
        "central_row_count":len(central),
        "gap_cutoff":D,"chosen_gap":d,
        "even_indices":[j1,j2],"map_images":[f1,f2],
        "pythagorean_legs":[4*d,v],"hypotenuse":L,
        "certificates":results,
    }

def main():
    out={"definition":"canonical z in [0,pN), full retained odd-mod4 family",
         "cases":[]}
    for h in (4096,16384,65536):
        for k,kind in enumerate(("identity","random_injection","dyadic_isometry")):
            seed=20261109+100*h+k
            out["cases"].append(solve(h,kind,seed))
    out["certificate_count"]=sum(len(c["certificates"]) for c in out["cases"])
    target=Path(__file__).with_suffix(".json")
    target.write_text(json.dumps(out,indent=2),encoding="utf-8")
    print(json.dumps({"status":"PASS","certificate_count":out["certificate_count"],
                      "cases":[{"height":c["height"],"map":c["map"],
                                "gap":c["chosen_gap"],"prime":c["prime"]}
                               for c in out["cases"]]},indent=2))

if __name__=="__main__":
    main()

