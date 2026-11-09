"""Compile exact forbidden black supports from every pair of rectangles."""
from itertools import combinations
from pathlib import Path
import json
import sys
import time

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles


def bits(mask):
    out=[]
    while mask:
        bit=mask&-mask
        out.append(bit)
        mask-=bit
    return out


def main():
    begin=time.monotonic()
    rects=rectangles(7,9)
    bysize={4:set(),6:set(),8:set()}
    for i,R in enumerate(rects):
        for T in rects[:i]:
            D=R^T
            bysize[D.bit_count()].add(D)
    print(json.dumps({'initial_supports':{k:len(v) for k,v in bysize.items()}}),flush=True)
    minimal={4:bysize[4],6:set(),8:set()}
    for D in bysize[6]:
        cells=bits(D)
        if not any(D-a-b in minimal[4] for a,b in combinations(cells,2)):
            minimal[6].add(D)
    print(json.dumps({'minimal_six':len(minimal[6]),'seconds':time.monotonic()-begin}),flush=True)
    for D in bysize[8]:
        cells=bits(D)
        if any(sum(c) in minimal[4] for c in combinations(cells,4)):
            continue
        if any(D-a-b in minimal[6] for a,b in combinations(cells,2)):
            continue
        minimal[8].add(D)
    data={'initial_supports':{k:len(v) for k,v in bysize.items()},
          'minimal_supports':{k:len(v) for k,v in minimal.items()},
          'elapsed_seconds':time.monotonic()-begin}
    if '--templates' in sys.argv:
        # Optional search templates are much larger than the count certificate.
        groups=[[[] for mask in range(128)] for col in range(9)]
        for family in minimal.values():
            for D in family:
                needed={}
                for bit in bits(D):
                    pos=bit.bit_length()-1
                    c,r=pos%9,pos//9
                    needed[c]=needed.get(c,0)|(1<<r)
                last=max(needed)
                at_last=needed.pop(last)
                others=[x for pair in sorted(needed.items()) for x in pair]
                for mask in range(128):
                    if mask&at_last==at_last:
                        groups[last][mask].append(others)
        data['groups']=groups
    (HERE/'seven_nine_differences.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
    print(json.dumps({k:v for k,v in data.items() if k!='groups'}),flush=True)


if __name__=='__main__':
    main()
