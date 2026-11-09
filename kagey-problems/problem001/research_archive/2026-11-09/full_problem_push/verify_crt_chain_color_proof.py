"""Standard-library RUP check for arbitrary saved CRT-chain color proofs."""
from collections import Counter
from hashlib import sha256
from itertools import combinations
from pathlib import Path
from time import monotonic
import argparse
import json
from verify_crt_chain_nonfourcolorable import load_cnf, rup, square


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--colors", type=int, required=True)
    ap.add_argument("--small", action="store_true")
    args = ap.parse_args()
    here = Path(__file__).resolve().parent
    c = args.colors
    if args.small:
        meta = json.loads((here/"crt_chain_small_five_chromatic.json").read_text())
        vertices = meta["vertices"]
        prefix = "crt_chain_small"
    else:
        meta = None
        vertices = list(range(150))
        prefix = "crt_chain_t375_n150"
    assert vertices == sorted(set(vertices)) and c >= 4
    indices = {v:i for i,v in enumerate(vertices)}
    edges = []
    for u,v in combinations(vertices, 2):
        k = 2*(v-u)
        if any(square(25*k*k+sign*6*375*k+375*375) is not None
               for sign in (-1,1)):
            edges.append((u,v))
    clique = (0,23,68,133)
    assert all((u,v) in edges for u,v in combinations(clique,2))
    var = lambda v,color: c*indices[v]+color+1
    expected = []
    for v in vertices:
        expected.append(tuple(var(v,color) for color in range(c)))
        expected.extend((-var(v,a),-var(v,b)) for a,b in combinations(range(c),2))
    expected.extend((-var(u,color),-var(v,color))
                    for u,v in edges for color in range(c))
    expected.extend((var(v,color),) for color,v in enumerate(clique))
    cnf_path = here/f"{prefix}_{c}color.cnf"
    proof_path = cnf_path.with_suffix(".drat")
    clauses = load_cnf(cnf_path, c*len(vertices))
    assert Counter(map(frozenset,clauses)) == Counter(map(frozenset,expected))
    if meta is not None:
        assert set(map(tuple,meta["edges"])) == set(edges)
        if "five_coloring" in meta:
            coloring = {int(v):color for v,color in meta["five_coloring"].items()}
            assert set(coloring) == set(vertices)
            assert all(0 <= color < 5 for color in coloring.values())
            assert all(coloring[u] != coloring[v] for u,v in edges)
    database, checked, deletes = list(clauses), [], 0
    start = monotonic()
    for line_number,line in enumerate(proof_path.read_text(encoding="ascii").splitlines(),1):
        fields = line.split()
        if not fields:
            continue
        if fields[0] == "d":
            deletes += 1
            continue
        values = list(map(int,fields))
        assert values[-1] == 0 and 0 not in values[:-1]
        learned = tuple(values[:-1])
        assert len(set(learned)) == len(learned)
        assert not any(-v in learned for v in learned)
        assert all(1 <= abs(v) <= c*len(vertices) for v in learned)
        rec = rup(database, learned)
        rec["proof_line"] = line_number
        checked.append(rec)
        database.append(learned)
        if len(checked) % 100 == 0:
            print(json.dumps({"checked_additions":len(checked),
                              "seconds":round(monotonic()-start,3)}),flush=True)
    assert checked and checked[-1]["learned"] == []
    result = {"status":"PASS","colors":c,"vertices":vertices,
              "edges":len(edges),"clauses":len(clauses),
              "rup_additions":len(checked),"ignored_deletions":deletes,
              "seconds":monotonic()-start,"checks":checked,
              "sha256":{p.name:sha256(p.read_bytes()).hexdigest()
                        for p in (cnf_path,proof_path,Path(__file__),
                                  here/"verify_crt_chain_nonfourcolorable.py")}}
    target = here/f"{prefix}_{c}color_independent_check.json"
    target.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:result[k] for k in
                      ("status","colors","edges","clauses","rup_additions","seconds")}))


if __name__ == "__main__":
    main()
