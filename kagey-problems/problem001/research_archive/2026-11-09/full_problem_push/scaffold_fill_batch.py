"""Bounded independent scaffold seeds followed by exact odd-row filling."""
from pathlib import Path
import json
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent


def run(script,args):
    result=subprocess.run([sys.executable,str(HERE/script)]+list(map(str,args)),
                          capture_output=True,text=True,timeout=140)
    if result.returncode:raise RuntimeError(result.stdout[-2000:]+result.stderr[-2000:])


def main():
    begin=time.monotonic();records=[]
    seeds=list(map(int,sys.argv[1:])) or [21,22,23,24]
    for seed in seeds:
        if time.monotonic()-begin>700:break
        run('constant_sea_order_sat.py',[15,60,'cadical195',seed,0,'empty'])
        source=f'constant_sea_h15_cadical195_seed{seed}_empty.json'
        core=json.loads((HERE/source).read_text());record={'seed':seed,'core_status':core['status']}
        if core['status']=='SAT':
            run('verify_sparse_board.py',[source])
            run('single_cell_extension_constraints.py',[source])
            unary=json.loads((HERE/source.replace('.json','_unary.json')).read_text())
            record['minimum_odd_domain']=unary['minimum_odd_row_domain']
            if unary['empty_odd_row_domains']:record['fill_status']='UNSAT_unary'
            else:
                run('pinned_sea_fiber_sat.py',[source,'odd',120,'cadical195'])
                target=f'pinned_fiber_{Path(source).stem}_odd_cadical195.json'
                filled=json.loads((HERE/target).read_text());record['fill_status']=filled['status']
                record['fill_file']=target
        records.append(record)
        out={'wall_seconds':time.monotonic()-begin,'requested_seeds':seeds,'results':records}
        tag='_'.join(map(str,seeds))
        (HERE/f'scaffold_fill_batch_{tag}.json').write_text(json.dumps(out,indent=2)+'\n')
        print(json.dumps(record),flush=True)
        if record.get('fill_status')=='SAT':break
    print(json.dumps({'finished':True,'wall_seconds':time.monotonic()-begin}),flush=True)


if __name__=='__main__':main()
