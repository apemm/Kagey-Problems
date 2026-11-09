"""Generate every reflected balanced row-partition representative upper model."""
from itertools import combinations
import argparse
import json
from pathlib import Path
from export_sea_residuals import export

parser=argparse.ArgumentParser()
parser.add_argument('--height',type=int,default=7)
parser.add_argument('--span',type=int,default=6)
args=parser.parse_args()
h=args.height
root=Path(__file__).resolve().parent
parts=[]
for part in combinations(range(1,h+1),h//2):
    reflected=tuple(sorted(h+1-r for r in part))
    if part>reflected:
        continue
    suffix='_p'+''.join(map(str,part))+f'_s{args.span}'
    path=root/f'sea_residuals_h{h}{suffix}.json'
    export(h,path,set(part),args.span)
    parts.append({'part':part,'suffix':suffix,'input':path.name})
manifest={'height':h,'span':args.span,'models':parts}
(root/f'partition_upper_models_h{h}_s{args.span}.json').write_text(json.dumps(manifest,indent=2)+'\n')
