"""Exact cliques in the fixed-offset P distance graph."""
from itertools import combinations
from math import isqrt
from pathlib import Path
import json


def certificate(offset, positions):
    edges = []
    relative_rows = list(positions) + [x-offset for x in positions]
    for i,j in combinations(range(len(positions)),2):
        candidates = []
        for source,target in ((i,j),(j,i)):
            d = positions[source]-positions[target]
            norm = 4*d*d+(offset+d)**2
            L = isqrt(norm)
            if L*L == norm:
                lo = (positions[source]+positions[target]-offset-L)//2
                hi = (positions[source]+positions[target]-offset+L)//2
                assert 2*lo == positions[source]+positions[target]-offset-L
                candidates.append((hi-lo,source,target,L,lo,hi))
        assert candidates, (offset,i,j)
        _,source,target,L,lo,hi = min(candidates)
        edges.append({"source":source,"target":target,"hypotenuse":L,
                      "relative_completion_rows":[lo,hi],
                      "completion_column":positions[source]+positions[target]})
        relative_rows += [lo,hi]
    shift = 1-min(relative_rows)
    if shift%2 == 0:
        shift += 1
    labels = [(shift+x,shift+x-offset) for x in positions]
    height = shift+max(relative_rows)
    for e in edges:
        e["completion_rows"] = [shift+x for x in e.pop("relative_completion_rows")]
        assert 1<=e["completion_rows"][0]<e["completion_rows"][1]<=height
    assert all(a%2==1 and b%2==0 and 1<=a<=height and 1<=b<=height
               for a,b in labels)
    return {"offset_a_minus_b":offset,"clique_order":len(positions),
            "relative_odd_rows":positions,"columns":[2*x for x in positions],
            "row_shift":shift,"height":height,"labels":labels,"edges":edges}


def main():
    results = [certificate(55,[0,8,30,50]),
               certificate(1045,[0,70,450,520,868])]
    output={"status":"PASS","certificates":results,
            "scope":"Explicit lower bounds of four and five colors; no unbounded-growth claim."}
    Path(__file__).with_name("constant_offset_clique_certificates.json").write_text(
        json.dumps(output,indent=2)+"\n")
    print(json.dumps({"status":"PASS","cliques":[
        {k:r[k] for k in ("offset_a_minus_b","clique_order","height","labels")}
        for r in results]}))


if __name__=="__main__":
    main()

