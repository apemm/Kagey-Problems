"""Independent rectangle certificates for the frozen periodic word 1,4,4."""
from pathlib import Path
import json
from verify_nonparity_sea_periods import independent_rects,direct

HERE=Path(__file__).resolve().parent


def violation(word,rects):
    seen={}
    for rect in rects:
        white=tuple(sorted((x,r) for x,r in rect if word[x]!=r))
        if len(white)>2:continue
        if not white:return {'kind':'hidden','rectangle':rect}
        if white in seen:return {'kind':'two tilted rectangles','rectangles':[seen[white],rect],'white':white}
        seen[white]=rect
        if len(white)==1:
            x,r=white[0]
            if (r-word[x])%2:return {'kind':'singleton axis rival','rectangle':rect,'white':white,'pair':[r,word[x]]}
        else:
            (x,r),(z,s)=white
            if x==z:
                if (r-s)%2:return {'kind':'vertical axis rival','rectangle':rect,'white':white}
            elif r==s:
                if word[x]==word[z]:return {'kind':'horizontal axis rival','rectangle':rect,'white':white,'axis_other_row':word[x]}
            elif word[x]==s and word[z]==r:
                return {'kind':'oblique axis rival','rectangle':rect,'white':white}
    return None


def main():
    period=(1,4,4)
    assert direct(period,independent_rects(23),{1,3,5,7})
    rects=independent_rects(64)
    word=[period[x%3] for x in range(64)]
    assert violation(word,rects) is None
    certificates=[]
    for phase in (1,2):
        for row in (1,2,3):
            changed=30+phase;copy=word.copy();copy[changed]=row
            result=violation(copy,rects);assert result is not None
            def move(rect):return [[x-changed,r] for x,r in rect]
            if 'rectangle' in result:result['rectangle']=move(result['rectangle'])
            if 'rectangles' in result:result['rectangles']=[move(R) for R in result['rectangles']]
            if 'white' in result:result['white']=move(result['white'])
            certificates.append({'phase':phase,'replacement':row,**result})
    out={'status':'PASS','height':7,'period':period,
         'periodic_validity_checked_width':23,'support_union_span_bound':20,
         'certificates':certificates}
    (HERE/'isolated_lowering_obstruction_check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__':main()
