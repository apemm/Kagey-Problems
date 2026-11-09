"""Independent geometric checks of the sparse parity-sea automaton."""
import itertools
import json
from pathlib import Path
import random
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'counting_followup'))
sys.path.insert(0,str(HERE.parents[2]))
from dominance_compatibility import compatibility,allowed
from verify_narrow import rectangles,axis_rectangles
from sea_sparse_automaton import forbidden_patterns,build_residuals,tilted_shapes


def accepts(transition,word):
    state=0
    for r in word:
        state=transition(state,r)
        if state is None:
            return False
    return True


def main():
    results=[]
    rng=random.Random(20261108)
    for h,n in ((4,8),(5,7),(6,5)):
        patterns,stats=forbidden_patterns(h,time.monotonic()+120)
        transition,nres=build_residuals(patterns,h)
        parity=set(range(1,h+1,2))
        count=0
        for word in itertools.product(range(1,h+1),repeat=n):
            assert accepts(transition,word)==allowed(compatibility(h,word),parity),(h,word)
            count+=1
        # Longer admissible walks, plus one-letter mutations, probe full spans.
        length=4*(1+(h-1)**2//4)+5
        random_checks=0
        for _ in range(200):
            word=[]
            state=0
            for _ in range(length):
                choices=[(r,transition(state,r)) for r in range(1,h+1)]
                choices=[(r,s) for r,s in choices if s is not None]
                if not choices:
                    break
                r,state=rng.choice(choices)
                word.append(r)
            assert accepts(transition,word)==allowed(compatibility(h,word),parity)
            random_checks+=1
            if word:
                word[rng.randrange(len(word))]=rng.randrange(1,h+1)
                assert accepts(transition,word)==allowed(compatibility(h,word),parity)
                random_checks+=1
        # Independent diagonal-based rectangle enumerator versus our side-vector
        # enumeration, over a full collision window.
        width=2*(1+(h-1)**2//4)+1
        axis=set(axis_rectangles(h,width))
        independent={frozenset((i%width,i//width+1) for i in range(h*width) if rect>>i&1)
                     for rect in rectangles(h,width) if rect not in axis}
        ours={frozenset((x+x0,r) for x,r in sh)
              for sh in tilted_shapes(h)
              for x0 in range(width-sh[-1][0])}
        assert independent==ours,(h,len(independent),len(ours))
        results.append({'height':h,'exhaustive_word_length':n,'exhaustive_words':count,
                        'long_walk_and_mutation_checks':random_checks,
                        'full_window_tilted_rectangles':len(ours),'status':'passed'})
    patterns,_=forbidden_patterns(6,time.monotonic()+120)
    transition,_=build_residuals(patterns,6)
    boundary=(1,1,6,1,4,6,4)
    assert allowed(compatibility(6,boundary),{1,3,5})
    assert not accepts(transition,boundary)
    for r in range(1,7):
        assert not allowed(compatibility(6,(r,)+boundary),{1,3,5})
    out={'checks':results,'finite_boundary_pruning':{'word':boundary,
         'finite_geometry_valid':True,'pattern_allowed':False,
         'all_six_left_extensions_invalid':True},'status':'passed'}
    (HERE/'sea_sparse_validation.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(out),flush=True)


if __name__=='__main__':
    main()
