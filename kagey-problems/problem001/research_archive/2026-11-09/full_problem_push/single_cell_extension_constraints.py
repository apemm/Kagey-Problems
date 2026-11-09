"""Exact unary sea restrictions for an already identifying sparse scaffold."""
from pathlib import Path
import json
import sys
import time

HERE=Path(__file__).resolve().parent
from verify_sparse_board import weak_rectangles
from constant_sea_order_sat import shapes


def unary_constraints(h,w,points):
    B={y*w+x for x,y in points}
    bitmask=sum(1<<p for p in B)
    weak=weak_rectangles(h,w,points)
    white={}
    for R in weak:
        remaining=R&~bitmask;P=[]
        while remaining:
            b=remaining&-remaining;P.append(b.bit_length()-1);remaining-=b
        assert len(P)<=2 and frozenset(P) not in white
        white[frozenset(P)]=R
    forbidden=set();witnesses={}
    def visit(corners):
        P=tuple(p for p in corners if p not in B)
        if not 1<=len(P)<=3:return
        for p in P:
            Q=frozenset(v for v in P if v!=p)
            if len(P)==1 or Q in white:
                forbidden.add(p)
                witnesses.setdefault(p,{'rectangle':list(corners),'presentation':list(P),
                                        'smaller_presentation':list(Q)})
    for x,y in points:
        for r in range(h):
            if r==y:continue
            for z in range(w):
                if z!=x:visit((y*w+x,y*w+z,r*w+x,r*w+z))
    for shape in shapes(h):
        span=max(x for x,y in shape)
        for left in range(w-span):
            visit(tuple(y*w+left+x for x,y in shape))
    return forbidden,witnesses,len(weak)


def main():
    source=HERE/sys.argv[1];data=json.loads(source.read_text());h=data['height']
    witness=next(e for e in data['events'] if e.get('status')=='SAT')
    columns=witness['columns_one_based'];w=len(columns)
    points=[(x,r-1) for x,C in enumerate(columns) for r in C]
    began=time.monotonic();bad,why,weak=unary_constraints(h,w,points)
    domains={x:[r+1 for r in range(h) if r*w+x not in bad] for x,C in enumerate(columns) if not C}
    odd_domains={x:[r for r in allowed if r%2] for x,allowed in domains.items()}
    out={'height':h,'width':w,'source':source.name,'seconds':time.monotonic()-began,
         'weak_rectangles':weak,'forbidden_points':len(bad),'all_row_domains':domains,
         'odd_row_domains':odd_domains,'empty_all_row_domains':[x for x,d in domains.items() if not d],
         'empty_odd_row_domains':[x for x,d in odd_domains.items() if not d],
         'minimum_all_row_domain':min(map(len,domains.values()),default=0),
         'minimum_odd_row_domain':min(map(len,odd_domains.values()),default=0),
         'forbidden_sea_points':[[p%w,p//w+1] for p in sorted(bad) if not columns[p%w]]}
    target=source.with_name(source.stem+'_unary.json')
    target.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('all_row_domains','odd_row_domains','forbidden_sea_points')}))


if __name__=='__main__':main()
