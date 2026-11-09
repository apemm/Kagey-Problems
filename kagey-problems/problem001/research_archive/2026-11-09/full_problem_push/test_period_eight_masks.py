"""Bounded tests of the three analytically surviving fixed period-eight seas."""
from pathlib import Path
import json
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent


def main():
    h=int(sys.argv[1]) if len(sys.argv)>1 else 15
    cap=float(sys.argv[2]) if len(sys.argv)>2 else 120
    q=h*h//4;budget=7*(q-1);begin=time.monotonic();results=[]
    for seed,mask in enumerate((8,10,42),101):
        args=[sys.executable,str(HERE/'constant_sea_order_sat.py'),str(h),str(cap),
              'cadical195',str(seed),str(budget),'spacing=8',f'pattern={mask}']
        if h==15:args.append('warm=constant_sea_h15_cadical195_seed91_high385_s8.json')
        subprocess.run(args,cwd=HERE,stdout=subprocess.DEVNULL,check=True,timeout=cap+30)
        name=f'constant_sea_h{h}_cadical195_seed{seed}_high{budget}_s8_mask{mask}.json'
        result=json.loads((HERE/name).read_text())
        rec={'mask':mask,'status':result['status'],'file':name,'seconds':result['wall_seconds']}
        results.append(rec);print(json.dumps(rec),flush=True)
    out={'height':h,'cap_per_mask':cap,'results':results,'seconds':time.monotonic()-begin}
    (HERE/f'period_eight_mask_search_h{h}.json').write_text(json.dumps(out,indent=2)+'\n')


if __name__=='__main__':main()
