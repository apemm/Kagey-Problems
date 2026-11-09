"""Independent exhaustive family audit using row-pair owners.

Unlike the incremental pair-shadow builder, validity is decided by repeated
pair owners and by checking all triples of rows for three distinct owners.
"""
from itertools import combinations, combinations_with_replacement
from pathlib import Path
import json
import time

HERE=Path(__file__).resolve().parent
ROWS=range(7)
PAIRS=list(combinations(ROWS,2))
TRIPLES=list(combinations(ROWS,3))


def valid(columns):
    owner={}
    for label,column in enumerate(columns):
        for pair in combinations(column,2):
            if pair in owner:
                return False
            owner[pair]=label
    for a,b,c in TRIPLES:
        x,y,z=owner.get((a,b)),owner.get((a,c)),owner.get((b,c))
        if x is not None and y is not None and z is not None and len({x,y,z})==3:
            return False
    return True


def mask(c):
    return sum(1<<r for r in c)


def reflect(p):
    return tuple(sorted(sum(1<<(6-r) for r in ROWS if b>>r&1) for b in p))


def main():
    begin=time.monotonic()
    counts=[]
    canonical=set()
    for t in range(5):
        count=0
        for triples in combinations(TRIPLES,t):
            if not valid(triples):
                continue
            allowed=[p for p in PAIRS if valid(triples+(p,))]
            for doubles in combinations(allowed,9-2*t):
                columns=triples+doubles
                if not valid(columns):
                    continue
                count+=1
                fixed=list(map(mask,columns))
                for singletons in combinations_with_replacement(ROWS,t):
                    p=tuple(sorted(fixed+[1<<r for r in singletons]))
                    canonical.add(min(p,reflect(p)))
        counts.append(count)
        print(json.dumps({'triples':t,'families':count,'seconds':time.monotonic()-begin}),flush=True)
    actual={tuple(p) for p in json.loads((HERE/'seven_nine_eighteen_data.json').read_text())['patterns']}
    assert counts==[12670,18480,3780,0,0]
    assert canonical==actual
    out={'status':'passed','independent_method':'full row-pair owner test',
         'nonsingleton_counts':counts,'representatives':len(canonical),
         'elapsed_seconds':time.monotonic()-begin}
    (HERE/'seven_nine_families_independent.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__':
    main()
