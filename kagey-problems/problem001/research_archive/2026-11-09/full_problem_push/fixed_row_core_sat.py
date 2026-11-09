"""Bounded exact SAT over row cores, with all singleton rows and orders free.

For widths12 or13 at excess10, fixed_excess_ten_cores.json is complete.
The parent records every solved core before enforcing the overall wall cap.
"""
from itertools import combinations
from pathlib import Path
import json
import multiprocessing as mp
import sys
import time
import traceback

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'.runtime'))
sys.path.insert(0,str(HERE.parents[2]))
from verify_narrow import rectangles,axis_rectangles,collision
from seven_row_equality_sat import bits,compact_supports


def encode(w,record,rects,flags,crop=True,known_bounds=None,axis_graph=None):
    core=record['masks'];empty=record['empty_columns']
    base=([0] if empty else [])+[1<<r for r in range(7)]
    types=base+core
    htypes=len(types);n=7*w
    tv=lambda c,j:n+htypes*c+j+1
    clauses=[]
    for c in range(w):
        clauses.append([tv(c,j) for j in range(htypes)])
        clauses.extend([-tv(c,j),-tv(c,k)] for j,k in combinations(range(htypes),2))
        for r in range(7):
            holders=[tv(c,j) for j,mask in enumerate(types) if mask>>r&1]
            clauses.extend([-v,r*w+c+1] for v in holders)
            clauses.append([-r*w-c-1]+holders)
    once=list(range(len(base),htypes))+([0] if empty else [])
    for j in once:
        clauses.append([tv(c,j) for c in range(w)])
        clauses.extend([-tv(c,j),-tv(d,j)] for c,d in combinations(range(w),2))
    clauses.append([tv(c,len(base)) for c in range((w+1)//2)])
    top=n+htypes*w
    if crop:
        from pysat.card import CardEnc,EncType
        double=[top+c+1 for c in range(w)]
        top+=w
        for c in range(w):
            present=[tv(c,j) for j in range(len(base),htypes)]
            clauses.append([-double[c]]+present)
            clauses.extend([-v,double[c]] for v in present)
        count=CardEnc.equals(double,bound=len(core),top_id=top,encoding=EncType.totalizer)
        clauses+=count.clauses;top=count.nv
        bounds={9:17,10:18,11:20,12:21} if known_bounds is None else known_bounds
        triple_types=[j for j,mask in enumerate(types) if mask.bit_count()==3]
        for length,bound in bounds.items():
            if length>=w:continue
            for left in range(w-length+1):
                columns=range(left,left+length)
                lits=[double[c] for c in columns]
                lits += [tv(c,j) for c in columns for j in triple_types]
                if empty:
                    lits += [-tv(c,0) for c in columns]
                    count_bound=bound
                else:count_bound=bound-length
                count=CardEnc.atmost(lits,bound=count_bound,top_id=top,encoding=EncType.totalizer)
                clauses+=count.clauses;top=count.nv
    owners={}
    for j,mask in enumerate(core):
        for a,b in combinations([r for r in range(7) if mask>>r&1],2):
            pair=(1<<a)|(1<<b)
            assert pair not in owners
            owners[pair]=j
    def possible(D):
        required={}
        for p in bits(D):required[p%w]=required.get(p%w,0)|(1<<(p//w))
        used=set()
        for mask in required.values():
            if mask.bit_count()<2:continue
            a=mask&-mask
            b=(mask^a)&-(mask^a)
            j=owners.get(a|b)
            if j is None or core[j]&mask!=mask or j in used:return False
            used.add(j)
        return True
    supports,info=compact_supports(rects,flags,w,None,
                                  set(owners) if axis_graph is None else axis_graph,possible)
    clauses.extend([-p-1 for p in bits(D)] for D in supports)
    info.update(variables=top,clauses=len(clauses),cropped_subboard_bounds=crop)
    return clauses,info


def worker(send,w,start,solver_name,end,crop):
    try:
        from pysat.solvers import Solver
        data=json.loads((HERE/'fixed_excess_ten_cores.json').read_text())
        rects=rectangles(7,w);axis=set(axis_rectangles(7,w))
        flags=[R not in axis for R in rects]
        for index in range(start,min(end,len(data['cores']))):
            began=time.monotonic()
            record=data['cores'][index]
            send.send({'event':'starting','index':index})
            clauses,info=encode(w,record,rects,flags,crop=crop)
            with Solver(name=solver_name,bootstrap_with=clauses) as solver:
                sat=solver.solve()
                result={'event':'result','index':index,'status':'SAT' if sat else 'UNSAT',
                        'seconds':time.monotonic()-began,'info':info,'solver_stats':solver.accum_stats()}
                if sat:
                    model=set(solver.get_model())
                    black=sum(1<<p for p in range(7*w) if p+1 in model)
                    assert black.bit_count()==w+10 and collision(rects,black) is None
                    points=sorted((p%w+1,p//w+1) for p in bits(black))
                    result['witness_one_based']=points
                    result['column_word']=','.join(''.join(str(r) for c,r in points if c==x)
                                                   for x in range(1,w+1))
                send.send(result)
                if sat:return
        send.send({'event':'complete'})
    except BaseException:
        send.send({'event':'error','traceback':traceback.format_exc()})
    finally:send.close()


def main():
    w=int(sys.argv[1]);assert w in (12,13)
    start=int(sys.argv[2]) if len(sys.argv)>2 else 0
    cap=float(sys.argv[3]) if len(sys.argv)>3 else 300
    solver=sys.argv[4] if len(sys.argv)>4 else 'cadical195'
    end=int(sys.argv[5]) if len(sys.argv)>5 else 2664
    crop='no-crop' not in sys.argv[6:]
    receive,send=mp.Pipe(duplex=False)
    child=mp.Process(target=worker,args=(send,w,start,solver,end,crop))
    begin=time.monotonic();child.start();send.close()
    results=[];current=start;complete=False;error=None
    def accept(event):
        nonlocal current,complete,error
        if event['event']=='starting':current=event['index']
        elif event['event']=='result':
            results.append(event)
            if len(results)%10==0 or event['status']=='SAT':
                print(json.dumps({k:v for k,v in event.items() if k not in ('witness_one_based','info','solver_stats')}),flush=True)
        elif event['event']=='complete':complete=True
        elif event['event']=='error':error=event['traceback']
    while child.is_alive() and time.monotonic()-begin<cap:
        try:
            if receive.poll(min(1,max(0,cap-time.monotonic()+begin))):accept(receive.recv())
        except (EOFError,OSError):break
    if child.is_alive():child.terminate()
    child.join(5)
    while True:
        try:
            if not receive.poll():break
            accept(receive.recv())
        except (EOFError,OSError):break
    sat=next((r for r in results if r['status']=='SAT'),None)
    status='error' if error else 'SAT' if sat else 'UNSAT_range' if complete else 'unknown'
    out={'rows':7,'columns':w,'target':w+10,'start_index':start,'end_exclusive':end,
         'status':status,'current_index':current,'completed_cores':len(results),
         'wall_seconds':time.monotonic()-begin,'cap_seconds':cap,'solver':solver,
         'cropped_subboard_bounds':crop,'results':results,'error':error}
    suffix='_crop' if crop else ''
    (HERE/f'fixed_core_h7_w{w}_{start}_{solver}{suffix}.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='results'}),flush=True)


if __name__=='__main__':
    mp.freeze_support();main()
