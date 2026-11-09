"""Bounded exact transition search from a completed board to a constant tail."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import time

from constant_sea_order_sat import shapes
from verify_parity_board_pair_geometry import check as check_parity_board

HERE=Path(__file__).resolve().parent


def main():
    source=HERE/sys.argv[1];data=json.loads(source.read_text());h=data['height']
    mode=sys.argv[2] if len(sys.argv)>2 else 'odd'
    source_tag=hashlib.sha256(source.read_bytes()).hexdigest()[:12]
    witness=next(e for e in data['events'] if e.get('status')=='SAT')
    columns=witness['columns_one_based']
    span=max(max(x for x,r in S) for S in shapes(h));length=2*span
    begin=time.monotonic();records=[];found=None
    for gap in (4,8,16,24,40,60):
        for row in ((1,h) if mode==f'1,{h}' else (1,h,2)):
            name=f'tail_frame_{source_tag}_h{h}_gap{gap}_row{row}.json'
            frame=columns[-length:]+[[] for _ in range(gap)]+[[row] for _ in range(length)]
            (HERE/name).write_text(json.dumps({'height':h,'skip_unary_domains':True,
                'events':[{'status':'SAT','columns_one_based':frame}]}))
            subprocess.run([sys.executable,str(HERE/'pinned_sea_fiber_sat.py'),
                            name,mode,'45','cadical195'],cwd=HERE,
                           stdout=subprocess.DEVNULL,check=True,timeout=65)
            mode_tag=mode if mode in ('all','odd') else 'rows'+'_'.join(mode.split(','))
            result_name='pinned_fiber_'+Path(name).stem+'_'+mode_tag+'_cadical195.json'
            result=json.loads((HERE/result_name).read_text())
            rec={'gap':gap,'row':row,'status':result['status'],'certificate':result_name}
            records.append(rec);print(json.dumps(rec),flush=True)
            if result['status']=='SAT':
                solved=next(e for e in result['events'] if e.get('status')=='SAT')
                full=columns[:-length]+solved['columns_one_based'];w=len(full)
                checked=check_parity_board(h,[{r-1 for r in C} for C in full])
                found={'status':'SAT','columns_one_based':full,'transition_columns':gap,
                       'tail_row':row,'tail_length':length,'width':w,
                       'black_points':checked['black_points'],
                       'weak_tilted_rectangles':checked['weak_tilted_rectangles'],
                       'independent_verifier':'black_pair_completion_and_axis_classification'}
                break
            if time.monotonic()-begin>500:break
        if found or time.monotonic()-begin>500:break
    out={'height':h,'source':source.name,'mode':mode,'local_memory':length,'attempts':records,
         'events':[found] if found else [],
         'status':'SAT' if found else 'no_witness_in_bounded_search',
         'seconds':time.monotonic()-begin}
    suffix='_tail' if mode=='odd' else '_tail_'+mode.replace(',','_')
    (HERE/(source.stem+suffix+'.json')).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('events','attempts')}))


if __name__=='__main__':main()
