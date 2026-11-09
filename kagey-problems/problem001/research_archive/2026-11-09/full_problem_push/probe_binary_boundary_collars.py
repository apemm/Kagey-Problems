"""Check both boundary colors on both ends of one binary-sea witness."""
from pathlib import Path
import hashlib
import json
import sys
import time

from constant_sea_order_sat import shapes,weak_templates,obstructions
from verify_sparse_board import weak_rectangles

HERE=Path(__file__).resolve().parent


def main():
    source=HERE/sys.argv[1];data=json.loads(source.read_text());h=data['height']
    found=next(e for e in data['events'] if e.get('status')=='SAT')
    columns=[{r-1 for r in C} for C in found['columns_one_based']]
    span=max(max(x for x,r in S) for S in shapes(h));length=2*span
    w=len(columns)+length;begin=time.monotonic()
    templates=weak_templates(h,w,high_allowed=True,spacing=8)
    results=[];events=[]
    for side in ('left','right'):
        for row in (0,h-1):
            pad=[{row} for _ in range(length)]
            cols=pad+columns if side=='left' else columns+pad
            # A left shift by length must preserve the marked-column residue.
            # Use all templates otherwise.
            ts=templates if side=='right' or length%8==0 else weak_templates(h,w,free_allowed=True)
            bad=obstructions(ts,cols)
            result={'side':side,'row':row+1,'valid':not bad,'positive_obstructions':len(bad)}
            if not bad:
                points=[(x,r) for x,C in enumerate(cols) for r in C]
                black=sum(1<<(r*w+x) for x,r in points)
                rects=weak_rectangles(h,w,points)
                assert len({R&~black for R in rects})==len(rects)
                events.append({'status':'SAT','columns_one_based':[sorted(r+1 for r in C) for C in cols],
                               'side':side,'row':row+1,'black_points':len(points),
                               'weak_rectangles':len(rects)})
            results.append(result);print(json.dumps(result),flush=True)
    out={'height':h,'source':source.name,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
         'core_width':len(columns),'collar_length':length,'results':results,'events':events,
         'seconds':time.monotonic()-begin}
    (HERE/(source.stem+'_binary_collars.json')).write_text(json.dumps(out,indent=2)+'\n')


if __name__=='__main__':main()
