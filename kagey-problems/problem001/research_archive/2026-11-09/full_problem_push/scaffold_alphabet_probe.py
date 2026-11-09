"""Bounded odd-plus-one-even sea alphabets for one verified scaffold."""
from pathlib import Path
import json
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent


def run(script,args,timeout=145):
    result=subprocess.run([sys.executable,str(HERE/script)]+list(map(str,args)),
                          capture_output=True,text=True,timeout=timeout)
    if result.returncode:raise RuntimeError(result.stdout[-2000:]+result.stderr[-2000:])


def main():
    source=sys.argv[1];even_rows=list(map(int,sys.argv[2:])) or [2,4,6,8,10,12,14]
    begin=time.monotonic();records=[]
    run('single_cell_extension_constraints.py',[source])
    for even in even_rows:
        rows=sorted(list(range(1,16,2))+[even]);alphabet=','.join(map(str,rows))
        run('pinned_sea_fiber_sat.py',[source,alphabet,120,'cadical195'])
        name=f'pinned_fiber_{Path(source).stem}_rows'+ '_'.join(map(str,rows))+'_cadical195.json'
        data=json.loads((HERE/name).read_text())
        record={'even_row':even,'status':data['status'],'file':name,'wall_seconds':data['wall_seconds']}
        records.append(record)
        tag='_'.join(map(str,even_rows))
        (HERE/f'alphabet_probe_{Path(source).stem}_{tag}.json').write_text(json.dumps({'results':records,'seconds':time.monotonic()-begin},indent=2)+'\n')
        print(json.dumps(record),flush=True)
        if data['status']=='SAT':break
    print(json.dumps({'finished':True,'seconds':time.monotonic()-begin}),flush=True)


if __name__=='__main__':main()
