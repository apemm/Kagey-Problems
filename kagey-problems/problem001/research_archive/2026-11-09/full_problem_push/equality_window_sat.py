"""Width14 equality-window necessary constraints, with the final full row graph."""
from itertools import combinations
from pathlib import Path
import json
import multiprocessing as mp
import sys
import time
import traceback

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'.runtime'))
from fixed_row_core_sat import encode,rectangles,axis_rectangles,collision


def catalog():
    reflect=lambda mask:sum(1<<(6-r) for r in range(7) if mask>>r&1)
    found={}
    for A in combinations(range(7),3):
        B=set(range(7))-set(A)
        full=tuple(sorted((1<<a)|(1<<b) for a in A for b in B))
        for removed in combinations(range(12),2):
            core=tuple(e for j,e in enumerate(full) if j not in removed)
            image=tuple(sorted(map(reflect,core)))
            if image<core:core=image;completion=tuple(sorted(map(reflect,full)))
            else:completion=full
            if core in found:assert found[core]==completion
            found[core]=completion
    out=[{'masks':list(core),'empty_columns':0,'full_masks':list(full)}
         for core,full in sorted(found.items())]
    assert len(out)==1164
    return out


def worker(send,start,end,solver_name):
    try:
        from pysat.solvers import Solver
        w=14;records=catalog();rects=rectangles(7,w);axis=set(axis_rectangles(7,w))
        flags=[R not in axis for R in rects]
        for index in range(start,min(end,len(records))):
            begin=time.monotonic();send.send({'event':'starting','index':index})
            record=records[index]
            clauses,info=encode(w,record,rects,flags,
                known_bounds={9:17,10:18,11:20,12:21,13:22},axis_graph=set(record['full_masks']))
            with Solver(name=solver_name,bootstrap_with=clauses) as solver:
                sat=solver.solve()
                result={'event':'result','index':index,'status':'SAT' if sat else 'UNSAT',
                        'seconds':time.monotonic()-begin,'info':info,'stats':solver.accum_stats()}
                if sat:
                    model=set(solver.get_model())
                    black=sum(1<<p for p in range(7*w) if p+1 in model)
                    assert black.bit_count()==24 and collision(rects,black) is None
                    result['column_word']=','.join(''.join(str(r+1) for r in range(7)
                                                         if black>>(r*w+c)&1) for c in range(w))
                send.send(result)
                if sat:return
        send.send({'event':'complete'})
    except BaseException:send.send({'event':'error','traceback':traceback.format_exc()})
    finally:send.close()


def main():
    start=int(sys.argv[1]) if len(sys.argv)>1 else 0
    cap=float(sys.argv[2]) if len(sys.argv)>2 else 1200
    solver=sys.argv[3] if len(sys.argv)>3 else 'cadical195'
    end=int(sys.argv[4]) if len(sys.argv)>4 else 1164
    (HERE/'equality_window14_cores.json').write_text(json.dumps({'cores':catalog()},indent=2)+'\n')
    receive,send=mp.Pipe(duplex=False)
    child=mp.Process(target=worker,args=(send,start,end,solver))
    begin=time.monotonic();child.start();send.close();results=[];current=start;complete=False;error=None
    def accept(event):
        nonlocal current,complete,error
        if event['event']=='starting':current=event['index']
        elif event['event']=='result':
            results.append(event)
            if len(results)%10==0 or event['status']=='SAT':
                print(json.dumps({k:v for k,v in event.items() if k not in ('info','stats')}),flush=True)
        elif event['event']=='complete':complete=True
        else:error=event['traceback']
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
    sat=any(r['status']=='SAT' for r in results)
    out={'height':7,'width':14,'target':24,'condition':'window in an equality board with final complete balanced row graph',
         'start_index':start,'end_exclusive':end,'current_index':current,'completed_cores':len(results),
         'status':'error' if error else 'SAT' if sat else 'UNSAT_range' if complete else 'unknown',
         'cap_seconds':cap,'wall_seconds':time.monotonic()-begin,'results':results,'error':error}
    (HERE/f'equality_window14_{start}_{solver}.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='results'}),flush=True)


if __name__=='__main__':mp.freeze_support();main()
