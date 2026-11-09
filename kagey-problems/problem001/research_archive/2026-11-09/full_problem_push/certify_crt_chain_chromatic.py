"""Certify the chromatic number of a finite rational CRT chain graph."""
import sys,json
from pathlib import Path
from itertools import combinations
from probe_rational_crt_chain_cliques import distances
HERE=Path(__file__).parent
sys.path.insert(0,str(HERE/".runtime"))
from pysat.solvers import Glucose3
N=150; D=distances(375,2);clique=[0,23,68,133]
records=[]
for colors in [5,6,7,8]:
    v=lambda x,c:colors*x+c+1
    clauses=[]
    for x in range(N):
        clauses.append([v(x,c) for c in range(colors)])
        clauses.extend([[-v(x,c),-v(x,d)] for c,d in combinations(range(colors),2)])
        for delta in D:
            if x+delta<N:clauses.extend([[-v(x,c),-v(x+delta,c)] for c in range(colors)])
    clauses.extend([[v(x,c)] for c,x in enumerate(clique)])
    with Glucose3(bootstrap_with=clauses,with_proof=True) as s:
        s.conf_budget(50000);answer=s.solve_limited()
        rec=dict(N=N,t=375,step=2,colors=colors,result=answer,stats=s.accum_stats())
        if answer is False:
            prefix=HERE/f"crt_chain_t375_n{N}_{colors}color"
            prefix.with_suffix(".cnf").write_text(
                f"p cnf {colors*N} {len(clauses)}\n"+
                "".join(" ".join(map(str,c))+" 0\n" for c in clauses),encoding="ascii")
            prefix.with_suffix(".drat").write_text("\n".join(s.get_proof())+"\n",encoding="ascii")
            rec.update(cnf=prefix.with_suffix(".cnf").name,proof=prefix.with_suffix(".drat").name)
        elif answer:
            model=set(s.get_model())
            coloring=[next(c for c in range(colors) if v(x,c) in model) for x in range(N)]
            assert all(coloring[x]!=coloring[x+d] for x in range(N) for d in D if x+d<N)
            rec["coloring"]=coloring
        records.append(rec)
        print(json.dumps({k:v for k,v in rec.items() if k!="coloring"}),flush=True)
        if answer:break
(HERE/"crt_chain_t375_n150_chromatic.json").write_text(json.dumps(records,indent=2)+"\n",encoding="utf-8")

