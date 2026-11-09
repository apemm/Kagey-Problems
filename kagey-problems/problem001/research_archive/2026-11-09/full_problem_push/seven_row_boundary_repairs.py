"""Small exact geometric repairs after deleting one column from known optima."""
from functools import lru_cache
from pathlib import Path
import json
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles,collision
from verify_seven_thirteen import side_rectangles


@lru_cache(None)
def geometry(w):return rectangles(7,w)


def valid(word):
    w=len(word)
    black=sum(1<<((r-1)*w+c) for c,col in enumerate(word) for r in col)
    return collision(geometry(w),black) is None


def main():
    begin=time.monotonic()
    core=tuple(tuple(map(int,c)) for c in
               '16,36,5,25,2,2,14,7,12,27,2,7,67,7,47,7,7,56,45,34,23'.split(','))
    full={tuple(sorted((a,b))) for a in (1,3,5,7) for b in (2,4,6)}
    states={core[1:],core[:-1]};results=[];checks=0
    for w in range(19,14,-1):
        found=set()
        for old in states:
            for removed,col in enumerate(old):
                word=old[:removed]+old[removed+1:]
                options=[]
                if len(col)==1:options=[word]
                else:
                    missing=full-{c for c in word if len(c)==2}
                    for c,single in enumerate(word):
                        if len(single)!=1:continue
                        for pair in missing:
                            if single[0] in pair:options.append(word[:c]+(pair,)+word[c+1:])
                for candidate in options:
                    if candidate in found:continue
                    checks+=1
                    if valid(candidate):found.add(candidate)
        chosen=sorted(found)[:16]
        if chosen:
            assert set(geometry(w))==side_rectangles(7,w)
        record={'width':w,'target':w+11,'valid_repairs_found':len(found),
                'kept':len(chosen),'column_words':[','.join(''.join(map(str,c)) for c in word)
                                                  for word in chosen],
                'presentations':len(geometry(w))}
        results.append(record);print(json.dumps(record),flush=True)
        if not chosen:break
        states=set(chosen)
    out={'status':'bounded_witness_search','results':results,'geometry_checks':checks,
         'seconds':time.monotonic()-begin}
    (HERE/'seven_row_boundary_repairs.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'checks':checks,'seconds':out['seconds']}))


if __name__=='__main__':main()
