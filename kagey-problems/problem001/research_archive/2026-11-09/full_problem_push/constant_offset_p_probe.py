"""Probe distance graphs of P rivals on a fixed b-a level."""
from collections import defaultdict, Counter
from math import gcd, isqrt
from pathlib import Path
import argparse
import json


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--height',type=int,default=10000)
    args = parser.parse_args()
    H=args.height-1
    distances=defaultdict(set)
    for p in range(2,isqrt(H)+1):
        for q in range(1,p):
            hyp=p*p+q*q
            if hyp>H or (p-q)%2==0 or gcd(p,q)>1:
                continue
            for scale in range(1,H//hyp+1,2):
                d=scale*p*q
                y=scale*(p*p-q*q)
                for u in {abs(y-d),y+d}:
                    if 0<u<=H:
                        distances[u].add(d)
    triangle_examples=[]
    nonbipartite=[]
    max_degree=0
    distribution=Counter()
    for u,D in sorted(distances.items()):
        assert u%2 and all(d%2==0 for d in D)
        common=0
        for d in D:
            common=gcd(common,d)
        if any((d//common)%2==0 for d in D):
            nonbipartite.append(dict(offset=u,distances=sorted(D)))
        tri=next(((a,b,a+b) for a in D for b in D if a<=b and a+b in D),None)
        if tri is not None:
            triangle_examples.append(dict(offset=u,triangle_distances=tri,
                                          distances=sorted(D)))
        max_degree=max(max_degree,len(D))
        distribution[len(D)]+=1
    result=dict(height=args.height,offsets_with_edges=len(distances),
                maximum_distance_count=max_degree,
                distance_count_histogram=dict(sorted(distribution.items())),
                nonbipartite_distance_sets=len(nonbipartite),
                first_nonbipartite=nonbipartite[:8],
                triangle_offsets=len(triangle_examples),
                first_triangles=triangle_examples[:8])
    path=Path(__file__).with_name(f'constant_offset_p_h{args.height}.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))


if __name__=='__main__':
    main()
