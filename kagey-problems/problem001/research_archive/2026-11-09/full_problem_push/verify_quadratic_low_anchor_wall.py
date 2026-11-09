"""Exact local check for low-row quadratic anchors and one complement splice."""
from threshold_progress_check import tilts
from pathlib import Path
import json

def color(y,beta): return (y*(y-1)//2+beta*y)%2

def check(word,beta,h=5):
    seen={}; issues=[]; weak=0
    for R in tilts(h):
        span=max(x for x,y in R)
        for s in range(len(word)-span):
            T=tuple((x+s,y) for x,y in R)
            white=tuple(p for p in T if word[p[0]]!=p[1])
            if len(white)>2: continue
            weak+=1
            if not white:
                issues.append(("hidden",T))
            elif white in seen:
                issues.append(("tilt_collision",T,seen[white],white))
            else: seen[white]=T
            rival=False
            if len(white)==1:
                x,y=white[0]; rival=color(y,beta)!=color(word[x],beta)
            elif len(white)==2:
                (x,y),(z,r)=white
                if x==z: rival=color(y,beta)!=color(r,beta)
                elif y==r: rival=word[x]==word[z]
                else: rival=word[x]==r and word[z]==y
            if rival: issues.append(("axis_rival",T,white))
    return {"length":len(word),"height":h,"weak":weak,"issues":issues[:20],"issue_count":len(issues)}

def word(x,kind):
    if kind=="q_complement":
        # The complement cut naturally creates four consecutive row-1 cells.
        return (2,2,1,1)[x%4] if x<0 else (1,1,2,2)[x%4]
    if kind=="qp_complement":
        # ...2233 | 3322..., instead choose a cut whose repeated block is row 2.
        w=(3,3,2,2)[x%4] if x<0 else (2,2,3,3)[x%4]
        return 1 if -2<=x<=1 else w
    if kind=="qp_left":
        return 1 if x<0 else (2,2,3,3)[x%4]
    if kind=="qp_periodic": return (2,2,3,3)[x%4]
    if kind=="q_periodic": return (1,1,2,2)[x%4]

out={}
for kind,beta in [("q_complement",0),("qp_complement",1),("qp_left",1),("qp_periodic",1),("q_periodic",0)]:
    seq=[word(x,kind) for x in range(-40,40)]
    out[kind]=check(seq,beta)
    out[kind]["central_word"]=seq[32:48]
Path(__file__).with_suffix(".json").write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))


