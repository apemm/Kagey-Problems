"""Independent seven-by-eight projected count using only 4/6-cell supports.

Every first-column mask is included. Each solver call and the entire run
are time bounded. Incomplete records never constitute an exact count.
"""
from pathlib import Path
from collections import defaultdict
from itertools import combinations
import argparse
import json
import multiprocessing as mp
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE/".runtime"))
H, W, TARGET = 7, 8, 16

def build():
    from pysat.card import CardEnc, EncType
    groups = defaultdict(list)
    cells = [(x,y,y*W+x) for y in range(H) for x in range(W)]
    for (x,y,p),(u,v,q) in combinations(cells,2):
        groups[(x+u,y+v,(x-u)**2+(y-v)**2)].append((p,q))
    rects = set()
    for diagonals in groups.values():
        for first,second in combinations(diagonals,2):
            vertices = set(first+second)
            assert len(vertices)==4
            rects.add(sum(1<<p for p in vertices))
    supports = set(rects)
    for a,b in combinations(rects,2):
        if a&b:
            supports.add(a^b)
    assert all(s.bit_count() in (4,6) for s in supports)
    clauses = [[-p-1 for p in range(H*W) if s>>p&1] for s in supports]
    top = H*W
    card = CardEnc.equals(list(range(1,top+1)),TARGET,top_id=top,
                          encoding=EncType.seqcounter)
    clauses.extend(card.clauses)
    top = card.nv
    # Established necessary bounds on contiguous subboards.
    bounds = {(7,7):14,(6,8):15,(6,7):13,(6,6):12,
              (5,6):11,(5,7):12,(3,8):10,(7,3):9}
    for height in range(3,H+1):
        for width in range(3,W+1):
            if (height,width) not in bounds:
                continue
            bound = min(width+(height*height)//4,
                        height+(width*width)//4)
            if height==3:
                bound=min(bound,width+2)
            if width==3:
                bound=min(bound,height+2)
            bound=min(bound,bounds.get((height,width),bound))
            if (height,width)==(H,W):
                continue
            for y0 in range(H-height+1):
                for x0 in range(W-width+1):
                    lits=[(y0+y)*W+x0+x+1
                          for y in range(height) for x in range(width)]
                    card=CardEnc.atmost(lits,bound,top_id=top,
                                        encoding=EncType.seqcounter)
                    clauses.extend(card.clauses)
                    top=max(top,card.nv)
    for x in range(W):
        lits=[y*W+x+1 for y in range(H)]
        card=CardEnc.atmost(lits,4,top_id=top,encoding=EncType.seqcounter)
        clauses.extend(card.clauses)
        top=max(top,card.nv)
        if x in (0,W-1):
            card=CardEnc.atleast(lits,2,top_id=top,encoding=EncType.seqcounter)
            clauses.extend(card.clauses)
            top=max(top,card.nv)
    for y in range(H):
        lits=[y*W+x+1 for x in range(W)]
        card=CardEnc.atmost(lits,5,top_id=top,encoding=EncType.seqcounter)
        clauses.extend(card.clauses)
        top=max(top,card.nv)
        if y in (0,H-1):
            clauses.append(lits)
    return clauses,sorted(rects),dict(rectangles=len(rects),
                                     supports=len(supports),
                                     variables=top,clauses=len(clauses))

def solve(send,mask,clauses,rects):
    try:
        from pysat.solvers import Solver
        fixed=[[y*W+1 if mask>>y&1 else -(y*W+1)] for y in range(H)]
        models=[]
        began=time.monotonic()
        with Solver(name="cadical195",bootstrap_with=clauses+fixed) as solver:
            while solver.solve():
                true={v for v in solver.get_model() if 0<v<=H*W}
                black=sum(1<<(v-1) for v in true)
                assert len(true)==TARGET
                assert len({r&~black for r in rects})==len(rects)
                assert sum(1<<y for y in range(H) if black>>(y*W)&1)==mask
                models.append(hex(black))
                solver.add_clause([-v for v in true])
            send.send(dict(status="complete",models=models,count=len(models),
                           seconds=time.monotonic()-began,
                           stats=solver.accum_stats()))
    except BaseException:
        send.send(dict(status="error",traceback=traceback.format_exc()))
    finally:
        send.close()

def shard(rank,workers,clauses,rects,per_case,seconds,masks=None,tag=""):
    suffix=f"{tag}_" if tag else ""
    path=HERE/f"seven_eight_independent_{suffix}shard_{rank}.jsonl"
    done=set()
    if path.exists():
        done={r["mask"] for r in map(json.loads,path.read_text().splitlines())
              if r["status"]=="complete"}
    began=time.monotonic()
    for mask in (list(range(128)) if masks is None else masks)[rank::workers]:
        if mask in done:
            continue
        remaining=seconds-(time.monotonic()-began)
        if remaining<=0:
            break
        receive,send=mp.Pipe(duplex=False)
        child=mp.Process(target=solve,args=(send,mask,clauses,rects))
        child.start()
        send.close()
        start=time.monotonic()
        result=None
        cap=min(per_case,remaining)
        while child.is_alive() and time.monotonic()-start<cap:
            if receive.poll(.1):
                try:
                    result=receive.recv()
                except EOFError:
                    pass
                break
        if child.is_alive():
            child.terminate()
        child.join(5)
        if result is None and receive.poll():
            try:
                result=receive.recv()
            except EOFError:
                pass
        receive.close()
        if result is None:
            result=dict(status="timeout")
        result.update(mask=mask,wall_seconds=time.monotonic()-start)
        with path.open("a",encoding="utf-8") as out:
            out.write(json.dumps(result,separators=(",",":"))+"\n")
        print(json.dumps({k:v for k,v in result.items()
                          if k not in ("models","stats")}),flush=True)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--workers",type=int,default=8)
    parser.add_argument("--per-case",type=float,default=450)
    parser.add_argument("--seconds",type=float,default=2100)
    parser.add_argument("--indices")
    parser.add_argument("--tag",default="")
    args=parser.parse_args()
    began=time.monotonic()
    clauses,rects,info=build()
    (HERE/"seven_eight_independent_encoding.json").write_text(
        json.dumps(info,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(dict(event="encoded",**info)),flush=True)
    children=[mp.Process(target=shard,args=(rank,args.workers,clauses,rects,
                                         args.per_case,args.seconds,
                                         None if args.indices is None else
                                         list(map(int,args.indices.split(","))),
                                         args.tag))
              for rank in range(args.workers)]
    for child in children:
        child.start()
    for child in children:
        child.join()
    print(json.dumps(dict(event="finished",seconds=time.monotonic()-began)),flush=True)

if __name__=="__main__":
    mp.freeze_support()
    main()

