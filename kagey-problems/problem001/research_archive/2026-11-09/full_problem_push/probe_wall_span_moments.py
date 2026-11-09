"""Exact central-corner span moments for pure and complemented affine phases."""
from math import gcd
import json, argparse, time
def moments(H):
    # Strip [0,2H], root at H. u,v positive primitive. Signed side
    # scales give two opposite-vertical and two same-vertical placements.
    op=ow=cp=cw=total=0
    for u in range(1,H+1):
        for v in range(1,H+1):
            if gcd(u,v)!=1:continue
            for k in range(1,H//v+1):
                ku=k*u;kv=k*v
                for ell in range(1,H//u+1):
                    lu=ell*u;lv=ell*v
                    mult=2+2*(kv+lu<=H)
                    span=ku+lv; gap=abs(ku-lv)
                    total+=mult*span
                    pureo=(kv%2==0 and lu%2==0)
                    purec=((k*(u+v))%2==0 and (ell*(u+v))%2==0)
                    if ku>=lv:
                        wallo=(kv%2==1 and lu%2==0)
                        wallc=((k*(u+v))%2==1 and (ell*(u+v))%2==0)
                    else:
                        wallo=(kv%2==0 and lu%2==1)
                        wallc=((k*(u+v))%2==0 and (ell*(u+v))%2==1)
                    op+=mult*span*pureo;ow+=mult*gap*wallo
                    cp+=mult*span*purec;cw+=mult*gap*wallc
    return dict(H=H,h=2*H+1,unrestricted=total,O_pure=op,O_wall_long_gap=ow,
                C_pure=cp,C_wall_long_gap=cw,O_ratio=ow/op,C_ratio=cw/cp,
                O_fraction=op/total,C_fraction=cp/total)
if __name__=="__main__":
    ap=argparse.ArgumentParser();ap.add_argument("--H",type=int,nargs="+",default=[32,64,128,256])
    ap.add_argument("--output",default="wall_span_moments.json");a=ap.parse_args()
    rows=[]
    for H in a.H:
        start=time.monotonic();r=moments(H);r["seconds"]=time.monotonic()-start
        rows.append(r);print(json.dumps(r),flush=True)
    with open(a.output,"w",encoding="utf-8") as f:json.dump(rows,f,indent=2);f.write("\n")

