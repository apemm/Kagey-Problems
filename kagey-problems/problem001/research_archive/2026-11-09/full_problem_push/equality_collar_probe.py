"""Check constant-row collars of the stored width-21 equality witness."""
from pathlib import Path
import hashlib
import json
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles,collision
from verify_seven_thirteen import side_rectangles


def black_mask(word):
    w=len(word)
    return sum(1<<((int(r)-1)*w+c) for c,col in enumerate(word) for r in col)


def main():
    begun=time.monotonic()
    source=HERE.parents[1]/'2026-11-07'/'data'/'res_h7_w21_p246.json'
    core=json.loads(source.read_text())['word'].split(',')
    h=7;W=(h-1)**2//2;L=2*W
    rects=rectangles(h,len(core)+L)
    assert set(rects)==side_rectangles(h,len(core)+L)
    result=[]
    for side in ('left','right'):
        for row in range(1,h+1):
            word=[str(row)]*L+core if side=='left' else core+[str(row)]*L
            black=black_mask(word)
            bad=collision(rects,black)
            rec={'side':side,'row':row,'valid':bad is None}
            if bad:
                w=len(word)
                rec['collision_rectangles']=[sorted((p%w+1,p//w+1) for p in range(h*w)
                                                    if R>>p&1) for R in bad]
            else:
                rec['column_word']=','.join(word)
                rec['black_cells']=black.bit_count()
                rec['presentations_checked']=len(rects)
            result.append(rec)
    out={'height':h,'core_width':len(core),'core_word':','.join(core),
         'source':str(source.relative_to(HERE.parents[2])),
         'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
         'collar_length':L,'rectangles':len(rects),'results':result,
         'seconds':time.monotonic()-begun}
    (HERE/'equality_width21_collar_check.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'collar_length':L,'successful':[{k:v for k,v in r.items() if k!='column_word'}
                                                   for r in result if r['valid']],
                      'seconds':out['seconds']}))


if __name__=='__main__':main()
