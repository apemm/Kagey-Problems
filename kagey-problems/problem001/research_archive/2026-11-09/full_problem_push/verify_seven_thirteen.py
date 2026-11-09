"""Two independent rectangle generators check the 23-point witness."""
from itertools import combinations
from pathlib import Path
import hashlib
import json
import sys

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles,mask,collision


def side_rectangles(h,w):
    out=set()
    for a,b in combinations(range(w),2):
        for r,s in combinations(range(h),2):
            out.add(mask(((a,r),(a,s),(b,r),(b,s)),w))
    for b in range(1,h):
        for d in range(1,h-b):
            for a in range(1,b*d+1):
                if b*d%a:continue
                c=b*d//a
                for x in range(w-a-c):
                    for y in range(b,h-d):
                        out.add(mask(((x,y),(x+a,y-b),(x+c,y+d),(x+a+c,y-b+d)),w))
    return out


def main():
    word='56,45,34,23,2,12,1,2,3,14,25,367,17'
    columns=[tuple(map(int,C)) for C in word.split(',')]
    B=mask([(x,r-1) for x,C in enumerate(columns) for r in C],13)
    first=rectangles(7,13);second=side_rectangles(7,13)
    assert set(first)==second and len(first)==2333
    assert B.bit_count()==23 and collision(first,B) is None
    presentations=[R&~B for R in second]
    assert len(set(presentations))==len(second)
    source=HERE/'fixed_core_h7_w13_100_cadical195_crop.json'
    data=json.loads(source.read_text())
    result=next(r for r in data['results'] if r['status']=='SAT')
    assert result['index']==996 and result['column_word']==word
    out={'status':'PASS','rows':7,'columns':13,'black_points':23,
         'column_word':word,'rectangles':len(first),'distinct_presentations':len(set(presentations)),
         'independent_generators':'equal diagonals and perpendicular integer sides',
         'upper_bound':'max(13+12-3, f(7,12)+2)=max(22,23)=23',
         'source_file':source.name,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
    (HERE/'seven_thirteen_exact_check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__':main()
