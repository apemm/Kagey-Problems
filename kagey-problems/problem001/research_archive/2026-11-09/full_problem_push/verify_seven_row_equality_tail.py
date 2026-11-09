"""Independent finite certificate for the eventual width-21 equality construction."""
from pathlib import Path
import hashlib
import json
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles,collision
from verify_seven_thirteen import side_rectangles


def main():
    begun=time.monotonic()
    core='16,36,5,25,2,2,14,7,12,27,2,7,67,7,47,7,7,56,45,34,23'.split(',')
    word=core+['1']*3+['2']*36
    w=len(word);assert w==60
    black=sum(1<<((int(r)-1)*w+c) for c,col in enumerate(word) for r in col)
    assert black.bit_count()==72
    doubles=sorted(tuple(map(int,col)) for col in word if len(col)==2)
    full=sorted(tuple(sorted((a,b))) for a in (1,3,5,7) for b in (2,4,6))
    assert doubles==full and all(len(col) in (1,2) for col in word)
    rects=rectangles(7,w)
    assert set(rects)==side_rectangles(7,w)
    assert collision(rects,black) is None
    hidden=sum(R&black==R for R in rects)
    assert hidden==0
    source=HERE/'equality_width21_tail_search.json'
    run=json.loads(source.read_text())
    assert run['status']=='witness' and run['witness']['checked_word']==','.join(word)
    assert run['witness']['transition']==['1']*3 and run['witness']['tail_row']==2
    # Tilted span <= 1+floor((h-1)^2/4); a common-corner pair has twice this span.
    tilted_span=1+6**2//4
    assert tilted_span==10 and 36>=2*tilted_span
    out={'status':'PASS','height':7,'all_widths_from':21,'finite_width':w,
         'black_cells':black.bit_count(),'distinct_presentations':len(rects),
         'hidden_rectangles':hidden,'full_parity_double_graph':doubles,
         'transition':['1']*3,'constant_tail_row':2,'checked_constant_tail_length':36,
         'tilted_span_bound':tilted_span,'pair_span_bound':2*tilted_span,
         'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
         'verification_seconds':time.monotonic()-begun}
    (HERE/'seven_row_equality_tail_check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__=='__main__':main()
