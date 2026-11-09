"""Exact width14,target25 search through 229 fixed row cores."""
from itertools import combinations
from pathlib import Path
import json
import multiprocessing as mp
import sys
import time
import traceback

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'.runtime'))
from fixed_row_core_sat import encode,rectangles,axis_rectangles,collision,bits


def catalog():
    reflected=lambda mask:sum(1<<(6-r) for r in range(7) if mask>>r&1)
    cores=set()
    for A in combinations(range(7),3):
        B=set(range(7))-set(A)
        full=tuple(sorted((1<<a)|(1<<b) for a in A for b in B))
        for omit in range(12):
            masks=full[:omit]+full[omit+1:]
            image=tuple(sorted(map(reflected,masks)))
            cores.add((0,min(masks,image)))
        image=tuple(sorted(map(reflected,full)))
        cores.add((1,min(full,image)))
    out=[{'empty_columns':empty,'masks':list(masks)} for empty,masks in sorted(cores)]
    assert len(out)==229
    assert sum(r['empty_columns']==0 for r in out)==210
    return out


def worker(send,start,end,solver_name,geometry):
    try:
        from pysat.solvers import Solver
        encoder=encode
        if geometry=='fiber':
            from fiber_fixed_core_encoding import encode as encoder
        w=14;records=catalog();rects=rectangles(7,w);axis=set(axis_rectangles(7,w))
        flags=[R not in axis for R in rects]
        for index in range(start,min(end,len(records))):
            began=time.monotonic();send.send({'event':'starting','index':index})
            clauses,info=encoder(w,records[index],rects,flags,
                                known_bounds={9:17,10:18,11:20,12:21,13:23})
            with Solver(name=solver_name,bootstrap_with=clauses) as solver:
                sat=solver.solve()
                result={'event':'result','index':index,'status':'SAT' if sat else 'UNSAT',
                        'seconds':time.monotonic()-began,'info':info,'stats':solver.accum_stats()}
                if sat:
                    model=set(solver.get_model())
                    black=sum(1<<p for p in range(7*w) if p+1 in model)
                    assert black.bit_count()==25 and collision(rects,black) is None
                    result['column_word']=','.join(''.join(str(r+1) for r in range(7)
                                                         if black>>(r*w+c)&1) for c in range(w))
                send.send(result)
                if sat:return
        send.send({'event':'complete'})
    except BaseException:send.send({'event':'error','traceback':traceback.format_exc()})
    finally:send.close()


def main():
    start=int(sys.argv[1]) if len(sys.argv)>1 else 0
    cap=float(sys.argv[2]) if len(sys.argv)>2 else 600
    solver=sys.argv[3] if len(sys.argv)>3 else 'cadical195'
    end=int(sys.argv[4]) if len(sys.argv)>4 else 229
    geometry=sys.argv[5] if len(sys.argv)>5 else 'compact'
    assert geometry in ('compact','fiber')
    records=catalog()
    (HERE/'fixed_excess_eleven_cores.json').write_text(json.dumps({'cores':records},indent=2)+'\n')
    receive,send=mp.Pipe(duplex=False)
    child=mp.Process(target=worker,args=(send,start,end,solver,geometry))
    began=time.monotonic();child.start();send.close();results=[];current=start;complete=False;error=None
    def accept(event):
        nonlocal current,complete,error
        if event['event']=='starting':current=event['index']
        elif event['event']=='result':
            results.append(event)
            print(json.dumps({k:v for k,v in event.items() if k not in ('info','stats')}),flush=True)
        elif event['event']=='complete':complete=True
        else:error=event['traceback']
    while child.is_alive() and time.monotonic()-began<cap:
        try:
            if receive.poll(min(1,max(0,cap-time.monotonic()+began))):accept(receive.recv())
        except (EOFError,OSError):break
    if child.is_alive():child.terminate()
    child.join(5)
    while True:
        try:
            if not receive.poll():break
            accept(receive.recv())
        except (EOFError,OSError):break
    sat=any(r['status']=='SAT' for r in results)
    out={'height':7,'width':14,'target':25,'start_index':start,'end_exclusive':end,
         'status':'error' if error else 'SAT' if sat else 'UNSAT_range' if complete else 'unknown',
         'current_index':current,'completed_cores':len(results),'cap_seconds':cap,
         'wall_seconds':time.monotonic()-began,'results':results,'error':error,'geometry':geometry}
    suffix='' if geometry=='compact' else '_fiber'
    (HERE/f'fixed_core_h7_w14_{start}_{solver}{suffix}.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='results'}),flush=True)


if __name__=='__main__':mp.freeze_support();main()
