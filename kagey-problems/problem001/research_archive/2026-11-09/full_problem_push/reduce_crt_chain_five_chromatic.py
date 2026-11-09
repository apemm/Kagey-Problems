"""Reduce the five-chromatic rational-chain witness and test five colors."""
from pathlib import Path
import sys, json
from itertools import combinations
from probe_rational_crt_chain_cliques import distances
sys.path.insert(0,str(Path(__file__).parent/".runtime"))
from pysat.solvers import Glucose3
D=set(distances(375,2)); clique=[0,23,68,133]
def cnf(vertices, colors):
    ids={x:i for i,x in enumerate(vertices)}
    v=lambda x,c:colors*ids[x]+c+1
    clauses=[]
    for x in vertices:
        clauses.append([v(x,c) for c in range(colors)])
        clauses += [[-v(x,c),-v(x,d)] for c,d in combinations(range(colors),2)]
    for x,y in combinations(vertices,2):
        if y-x in D:
            clauses += [[-v(x,c),-v(y,c)] for c in range(colors)]
    clauses += [[v(x,c)] for c,x in enumerate(clique) if x in ids]
    return clauses
V=list(range(150))
for x in sorted(V,key=lambda x:sum(abs(x-y) in D for y in V)):
    if x in clique:continue
    candidate=[y for y in V if y!=x]
    with Glucose3(bootstrap_with=cnf(candidate,4)) as s:
        s.conf_budget(10000);answer=s.solve_limited()
    if answer is False:V=candidate
clauses=cnf(V,4)
with Glucose3(bootstrap_with=clauses,with_proof=True) as s:
    assert s.solve() is False
    proof=s.get_proof()
base=Path(__file__).parent
(base/"crt_chain_small_4color.cnf").write_text(
    f"p cnf {4*len(V)} {len(clauses)}\n"+
    "".join(" ".join(map(str,c))+" 0\n" for c in clauses),encoding="ascii")
(base/"crt_chain_small_4color.drat").write_text("\n".join(proof)+"\n",encoding="ascii")
out=dict(vertices=V,distances=sorted(D),clique=clique,
         edges=[[x,y] for x,y in combinations(V,2) if y-x in D],
         cnf="crt_chain_small_4color.cnf",proof="crt_chain_small_4color.drat")
with Glucose3(bootstrap_with=cnf(V,5)) as s:
    assert s.solve()
    model=set(s.get_model())
    out["five_coloring"]={x:next(c for c in range(5) if 5*i+c+1 in model)
                          for i,x in enumerate(V)}
(base/"crt_chain_small_five_chromatic.json").write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8")
print(json.dumps(out),flush=True)
for N in [150,300,500,1000]:
    with Glucose3(bootstrap_with=cnf(list(range(N)),5)) as s:
        s.conf_budget(10000);answer=s.solve_limited()
        print(json.dumps(dict(N=N,colors=5,result=answer,stats=s.accum_stats())),flush=True)

