"""Independent diagonal-based periodic checks of two full height-seven sea models."""
from itertools import product
from pathlib import Path
import hashlib
import importlib.util
import json
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles,axis_rectangles
SOURCE=HERE.parents[1]/'2026-11-08/dominance_bridge/sea_sparse_automaton.py'
spec=importlib.util.spec_from_file_location('sea_audit_source',SOURCE)
sea=importlib.util.module_from_spec(spec);spec.loader.exec_module(sea)


def independent_rects(w):
    axis=set(axis_rectangles(7,w))
    return [tuple((p%w,p//w+1) for p in range(7*w) if R>>p&1)
            for R in rectangles(7,w) if R not in axis]


def direct(period,rects,block):
    seen=set();length=len(period)
    separated=lambda r,s:(r in block)!=(s in block)
    for rect in rects:
        white=tuple(sorted((x,r) for x,r in rect if period[x%length]!=r))
        if len(white)>2:continue
        if not white or white in seen:return False
        seen.add(white)
        if len(white)==1:
            x,r=white[0]
            if separated(r,period[x%length]):return False
        else:
            (x,r),(z,s)=white
            if x==z:
                if separated(r,s):return False
            elif r==s:
                if period[x%length]==period[z%length]:return False
            elif period[x%length]==s and period[z%length]==r:return False
    return True


def main():
    begin=time.monotonic();checks=[]
    geometry={p:independent_rects(p+20) for p in range(1,5)}
    for block in ({1,3,5,7},{1,3,6}):
        patterns,stats=sea.forbidden_patterns(7,time.monotonic()+120,part=block)
        step,nres=sea.build_residuals(patterns,7)
        periods=[]
        for p in range(1,5):
            count=0;accepted=0
            for word in product(range(1,8),repeat=p):
                state=0;model=True
                for i in range(p+20):
                    state=step(state,word[i%p])
                    if state is None:model=False;break
                actual=direct(word,geometry[p],block)
                assert model==actual,(block,word,model,actual)
                count+=1;accepted+=actual
            periods.append({'period':p,'words':count,'accepted':accepted})
        checks.append({'block':sorted(block),'residuals':nres,'geometry':stats,'periods':periods})
    exported=json.loads((HERE/'sea_residuals_h7_p136.json').read_text())
    assert exported['partition']==[1,3,6] and exported['height']==7
    assert exported['count']==checks[1]['residuals']==7950
    assert 'truncation_span' not in exported['geometry']
    assert exported['geometry']['maximum_pattern_span']==20
    assert exported['geometry']['minimal_patterns']==3151
    out={'status':'PASS','checks':checks,'nonparity_input_full_not_truncated':True,
         'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
         'export_sha256':hashlib.sha256((HERE/'sea_residuals_h7_p136.json').read_bytes()).hexdigest(),
         'seconds':time.monotonic()-begin}
    (HERE/'nonparity_sea_periodic_audit.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__':main()
