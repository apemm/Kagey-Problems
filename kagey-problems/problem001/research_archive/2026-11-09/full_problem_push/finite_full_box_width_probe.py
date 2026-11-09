"""Bounded sharpness search for the nine-column full-box classification."""
from itertools import combinations,product
from pathlib import Path
import json
import time
import sys
import row_class_phase_sft as engine

HERE=Path(__file__).resolve().parent


def main():
    width=int(sys.argv[1]) if len(sys.argv)>1 else 8
    heights=list(map(int,sys.argv[2:])) or [8,9,10,11,12]
    begin=time.monotonic();records=[];witness=None
    for h in heights:
        shapes=engine.engine.tilted_shapes(h)
        expected=engine.expected_parts(h)
        parts=sorted({engine.representative(h,A) for A in combinations(range(1,h+1),h//2)})
        checked=0
        for A in parts:
            if A in expected:continue
            patterns=engine.forbidden_phase_patterns(h,A,shapes)
            translated=[tuple((x+j,a-1) for x,a in P) for P in patterns
                        for j in range(width-P[-1][0])]
            checked+=1
            for word in product(range(2),repeat=width):
                if not any(all(word[x]==a for x,a in P) for P in translated):
                    witness={'height':h,'width':width,'one_class':A,'phase':word}
                    break
            if witness:break
        records.append({'height':h,'nonprotected_partitions_checked':checked,
                        'witness':witness})
        print(json.dumps(records[-1]),flush=True)
        if witness:break
    out={'scope':'singleton and vertical-axis rivals only','width':width,
         'records':records,'seconds':time.monotonic()-begin}
    (HERE/f'finite_full_box_width{width}_probe.json').write_text(json.dumps(out,indent=2)+'\n')


if __name__=='__main__':main()
