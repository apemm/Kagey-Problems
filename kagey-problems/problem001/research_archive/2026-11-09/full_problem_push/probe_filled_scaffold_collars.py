"""Check every immediate constant collar of a completed parity board."""
from pathlib import Path
import hashlib
import json
import sys
import time

from constant_sea_order_sat import shapes, weak_templates, obstructions
from verify_sparse_board import weak_rectangles

HERE=Path(__file__).resolve().parent


def main():
    source=HERE/sys.argv[1]
    saved=json.loads(source.read_text());h=saved['height']
    witness=next(e for e in saved['events'] if e.get('status')=='SAT')
    cols=[{r-1 for r in C} for C in witness['columns_one_based']]
    span=max(max(x for x,r in S) for S in shapes(h))
    length=2*span;w=len(cols)+length
    begin=time.monotonic()
    templates=weak_templates(h,w,free_allowed=True)
    results=[]
    for side in ('left','right'):
        for row in range(h):
            tail=[{row} for _ in range(length)]
            padded=tail+cols if side=='left' else cols+tail
            bad=obstructions(templates,padded)
            rec={'side':side,'row':row+1,'valid':not bad,
                 'positive_obstructions':len(bad)}
            if bad:
                rec['first_support']=[[x+1,r+1] for x,r in sorted(next(iter(bad)))]
            else:
                points=[(x,r) for x,C in enumerate(padded) for r in C]
                B=sum(1<<(r*w+x) for x,r in points)
                rects=weak_rectangles(h,w,points)
                presentations={R&~B for R in rects}
                assert len(presentations)==len(rects)
                rec['independent_weak_rectangles']=len(rects)
                rec['columns_one_based']=[sorted(r+1 for r in C) for C in padded]
            results.append(rec)
            print(json.dumps({k:v for k,v in rec.items() if k!='columns_one_based'}),flush=True)
    out={'height':h,'source':source.name,
         'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
         'core_width':len(cols),'tilted_span':span,'collar_length':length,
         'results':results,'seconds':time.monotonic()-begin}
    (HERE/(source.stem+'_collars.json')).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'finished':True,'successes':sum(r['valid'] for r in results),
                      'seconds':out['seconds']}))


if __name__=='__main__':main()
