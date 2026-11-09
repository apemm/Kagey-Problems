"""Bounded order repair using exact local odd-sea UNSAT cores."""
from pathlib import Path
import json
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
PATTERNS='h15_odd_filling_order_patterns.json'


def run(script,args,timeout=145):
    result=subprocess.run([sys.executable,str(HERE/script)]+list(map(str,args)),
                          capture_output=True,text=True,timeout=timeout)
    if result.returncode:raise RuntimeError(result.stdout[-2000:]+result.stderr[-2000:])


def result(path):
    saved=json.loads((HERE/path).read_text())
    final=next((e for e in reversed(saved.get('events',[])) if e.get('status') in ('SAT','UNSAT')),None)
    return saved,final


def main():
    initial='pinned_fiber_guard_core_h15_six_pad2_odd_guarded_minimal_glucose4.json'
    if not (HERE/PATTERNS).exists():
        data,final=result(initial)
        patterns=[{'span_slots':10,'entries':final['forbidden_partial_order'],'certificate':initial}]
    else:patterns=json.loads((HERE/PATTERNS).read_text())['patterns']
    current='constant_sea_h15_cadical195_seed17_empty.json'
    begin=time.monotonic();records=[]
    seeds=list(map(int,sys.argv[1:])) or [25,26,27,28]
    for seed in seeds:
        if time.monotonic()-begin>900:break
        (HERE/PATTERNS).write_text(json.dumps({'height':15,'sea_rows':'odd','patterns':patterns},indent=2)+'\n')
        run('constant_sea_order_sat.py',[15,60,'cadical195',seed,0,'empty',f'warm={current}',f'blocked={PATTERNS}'])
        candidate=f'constant_sea_h15_cadical195_seed{seed}_empty.json'
        data,final=result(candidate);record={'seed':seed,'core_status':data['status'],'patterns_before':len(patterns)}
        if data['status']!='SAT':
            records.append(record);print(json.dumps(record),flush=True);continue
        run('verify_sparse_board.py',[candidate]);current=candidate
        run('pinned_sea_fiber_sat.py',[current,'odd',120,'glucose4','guarded','minimize'])
        fill=f'pinned_fiber_{Path(current).stem}_odd_guarded_minimal_glucose4.json'
        data,final=result(fill);record['fill_status']=data['status'];record['fill_file']=fill
        if final and final['status']=='UNSAT':
            entries=final['forbidden_partial_order']
            left=max(0,min(e['slot'] for e in entries)-2)
            right=min(55,max(e['slot'] for e in entries)+2)
            source,_=result(current);board=next(e for e in source['events'] if e.get('status')=='SAT')
            crop=f'h15_repair_seed{seed}_local.json'
            local={'height':15,'final_parity_graph':True,'crop_slots':[left,right],
                   'events':[{'status':'SAT','columns_one_based':board['columns_one_based'][4*left:4*right+1]}]}
            (HERE/crop).write_text(json.dumps(local,indent=2)+'\n')
            run('pinned_sea_fiber_sat.py',[crop,'odd',60,'glucose4','guarded','minimize'])
            local_fill=f'pinned_fiber_{Path(crop).stem}_odd_guarded_minimal_glucose4.json'
            local_data,local_final=result(local_fill)
            if local_final and local_final['status']=='UNSAT':
                patterns.append({'span_slots':right-left+1,'entries':local_final['forbidden_partial_order'],
                                 'certificate':local_fill})
                record['learned_span']=right-left+1;record['learned_labels']=len(local_final['forbidden_partial_order'])
            else:
                patterns.append({'span_slots':56,'entries':entries,'certificate':fill})
                record['learned_span']=56;record['learned_labels']=len(entries)
        records.append(record)
        (HERE/PATTERNS).write_text(json.dumps({'height':15,'sea_rows':'odd','patterns':patterns},indent=2)+'\n')
        tag='_'.join(map(str,seeds))
        (HERE/f'h15_order_repair_{tag}.json').write_text(json.dumps({'wall_seconds':time.monotonic()-begin,'results':records},indent=2)+'\n')
        print(json.dumps(record),flush=True)
        if final and final['status']=='SAT':break
        if final is None or data['status']=='unknown':break
    print(json.dumps({'finished':True,'seconds':time.monotonic()-begin}),flush=True)


if __name__=='__main__':main()
