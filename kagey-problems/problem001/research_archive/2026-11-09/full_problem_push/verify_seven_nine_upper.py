"""Independent Python enumeration, with independent rectangle enumeration.

Checks the 957 vertical-reflection representatives, without the horizontal
reflection reduction of the JavaScript search. A time cap is inconclusive.
"""
from pathlib import Path
import json
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
import verify_narrow


def main():
    started=time.monotonic()
    deadline=started+120
    data=json.loads((HERE/'seven_nine_search_data.json').read_text())
    last=[[] for _ in range(9)]
    rectangles=verify_narrow.rectangles(7,9)
    for bits in rectangles:
        points=tuple((i%9,i//9) for i in range(63) if bits>>i&1)
        if len({p[0] for p in points})==2 and len({p[1] for p in points})==2:
            continue
        last[max(x for x,r in points)].append(points)
    assert sum(map(len,last))==357 and len(rectangles)==1113
    nodes=0
    timed_out=False
    witness=None
    cases=[]
    for number,masks in enumerate(data['patterns']):
        blocks=[frozenset(r for r in range(7) if mask>>r&1) for mask in masks]
        pairs={frozenset((r,s)) for b in blocks for r in b for s in b if r!=s}
        word=[]
        presentations=set()
        before=nodes

        def visit(available):
            nonlocal nodes,timed_out,witness
            nodes+=1
            if nodes%4096==0 and time.monotonic()>deadline:
                timed_out=True
                return False
            if not available:
                witness=[sorted(b) for b in word]
                return True
            x=len(word)
            for chosen in available:
                word.append(blocks[chosen])
                additions=[]
                valid=True
                for rectangle in last[x]:
                    white=frozenset((c,r) for c,r in rectangle if r not in word[c])
                    if len(white)>2:
                        continue
                    if len(white)==1:
                        c,r=next(iter(white))
                        if any(frozenset((r,s)) in pairs for s in word[c]):
                            valid=False
                            break
                    elif len(white)==2:
                        (c,r),(d,s)=tuple(white)
                        rival=(c==d and frozenset((r,s)) in pairs)
                        rival|=(r==s and bool(word[c]&word[d]))
                        rival|=(c!=d and r!=s and s in word[c] and r in word[d])
                        if rival:
                            valid=False
                            break
                    if white in presentations:
                        valid=False
                        break
                    presentations.add(white)
                    additions.append(white)
                if valid and visit(tuple(i for i in available if i!=chosen)):
                    return True
                for white in additions:
                    presentations.remove(white)
                word.pop()
                if timed_out:
                    return False
            return False

        sat=visit(tuple(range(9)))
        cases.append({'index':number,'nodes':nodes-before,'status':'SAT' if sat else 'incomplete' if timed_out else 'UNSAT'})
        if sat or timed_out:
            break
    out={'status':'SAT' if witness else 'incomplete' if timed_out else 'UNSAT',
         'representatives_checked':len(cases),'nodes':nodes,
         'rectangles':len(rectangles),'tilted_rectangles':sum(map(len,last)),
         'horizontal_reflection_reduction':False,
         'witness_zero_based_rows':witness,'cases':cases,
         'elapsed_seconds':time.monotonic()-started}
    (HERE/'seven_nine_upper_independent.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='cases'}),flush=True)


if __name__=='__main__':
    main()
