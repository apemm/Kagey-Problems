"""Bounded SAT coloring probes for the normalized rational CRT P chain."""
from pathlib import Path
import sys, json
from itertools import combinations
from probe_rational_crt_chain_cliques import distances
sys.path.insert(0, str(Path(__file__).parent / ".runtime"))
from pysat.solvers import Glucose3

D = distances(375, 2)
clique = [0, 23, 68, 133]
assert all(abs(x-y) in D for x,y in combinations(clique,2))
out = Path(__file__).with_suffix(".jsonl")
for N in [150, 200, 300, 500, 1000, 2000]:
    def v(x,c): return 4*x+c+1
    clauses=[]
    for x in range(N):
        clauses.append([v(x,c) for c in range(4)])
        clauses += [[-v(x,c),-v(x,d)] for c,d in combinations(range(4),2)]
        for delta in D:
            if x+delta < N:
                clauses += [[-v(x,c),-v(x+delta,c)] for c in range(4)]
    clauses += [[v(x,c)] for c,x in enumerate(clique)]
    with Glucose3(bootstrap_with=clauses, with_proof=True) as solver:
        solver.conf_budget(20000)
        result=solver.solve_limited()
        rec=dict(t=375, step=2, N=N, distances=D, colors=4, result=result,
                 stats=solver.accum_stats())
        if result:
            model=set(solver.get_model())
            coloring=[next(c for c in range(4) if v(x,c) in model) for x in range(N)]
            assert all(coloring[x]!=coloring[x+d] for x in range(N) for d in D if x+d<N)
            rec["coloring"]=coloring
        elif result is False:
            proof=solver.get_proof()
            proof_path=out.with_name(f"crt_chain_t375_n{N}_4color.drat")
            proof_path.write_text("\n".join(proof)+"\n",encoding="ascii")
            rec["proof"]=proof_path.name
            cnf_path=proof_path.with_suffix(".cnf")
            cnf_path.write_text(f"p cnf {4*N} {len(clauses)}\n"+
                "".join(" ".join(map(str,c))+" 0\n" for c in clauses),encoding="ascii")
            rec["cnf"]=cnf_path.name
        with out.open("a",encoding="utf-8") as f:
            f.write(json.dumps(rec)+"\n")
        print(json.dumps({k:v for k,v in rec.items() if k!="coloring"}),flush=True)
        if result is False:break

