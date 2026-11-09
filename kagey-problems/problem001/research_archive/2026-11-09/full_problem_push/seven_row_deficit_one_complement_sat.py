"""Complete-core continuation with complementary cropped-window constraints."""
from pathlib import Path
import hashlib
import json
import multiprocessing as mp
import sys
import time
import traceback

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'.runtime'))
from fixed_excess_eleven_sat import catalog
from fixed_row_core_sat import encode,rectangles,axis_rectangles,collision

BOUNDS={9:17,10:18,11:20,12:21,13:22,14:24,15:25,16:26}


def worker(send,w,index,solver_name):
    try:
        from pysat.solvers import Solver
        begun=time.monotonic();record=catalog()[index]
        rects=rectangles(7,w);axis=set(axis_rectangles(7,w))
        clauses,info=encode(w,record,rects,[r not in axis for r in rects],known_bounds=BOUNDS)
        # The exact total is w+11. Each inside-window upper bound therefore
        # gives an equivalent lower bound on its complementary columns.
        # Writing that lower bound explicitly avoids relying on propagation
        # between two overlapping cardinality networks.
        from pysat.card import CardEnc,EncType
        n=7*w;empty=record['empty_columns'];base_types=7+empty
        htypes=base_types+len(record['masks'])
        double=lambda c:n+htypes*w+c+1
        empty_type=lambda c:n+htypes*c+1
        top=info['variables'];extra=0
        for length,bound in BOUNDS.items():
            if length>=w:continue
            for left in range(w-length+1):
                outside=[c for c in range(w) if not left<=c<left+length]
                lits=[double(c) for c in outside]
                need=11+length-bound
                if empty:
                    lits += [-empty_type(c) for c in outside]
                    need += len(outside)
                count=CardEnc.atleast(lits,bound=need,top_id=top,encoding=EncType.totalizer)
                clauses+=count.clauses;extra+=len(count.clauses);top=count.nv
        info.update(variables=top,clauses=len(clauses),complementary_crop_clauses=extra)
        send.send({'event':'encoded','info':info})
        with Solver(name=solver_name,bootstrap_with=clauses) as solver:
            sat=solver.solve()
            out={'index':index,'status':'SAT' if sat else 'UNSAT',
                 'seconds':time.monotonic()-begun,'info':info,'stats':solver.accum_stats()}
            if sat:
                model=set(solver.get_model())
                black=sum(1<<p for p in range(7*w) if p+1 in model)
                assert black.bit_count()==w+11 and collision(rects,black) is None
                out['column_word']=','.join(''.join(str(r+1) for r in range(7)
                                                   if black>>(r*w+c)&1) or '0' for c in range(w))
                out['black_hex']=hex(black)
            send.send({'event':'result',**out})
    except BaseException:send.send({'event':'error','traceback':traceback.format_exc()})
    finally:send.close()


def priority(records):
    parity={(1<<a)|(1<<b) for a in (0,2,4,6) for b in (1,3,5)}
    return sorted(range(len(records)),key=lambda i:(not set(records[i]['masks'])<=parity,
                                                  records[i]['empty_columns'],i))


def main():
    w=int(sys.argv[1]);assert 17<=w<=19
    total=float(sys.argv[2]) if len(sys.argv)>2 else 300
    each=float(sys.argv[3]) if len(sys.argv)>3 else 30
    solver=sys.argv[4] if len(sys.argv)>4 else 'cadical195'
    tag=sys.argv[5] if len(sys.argv)>5 else 'pilot'
    records=catalog();order=priority(records);results=[];begin=time.monotonic()
    destination=HERE/f'deficit_one_h7_w{w}_{tag}_{solver}.json'
    def save():
        sat=any(r['status']=='SAT' for r in results)
        complete=len(results)==len(records) and all(r['status']=='UNSAT' for r in results)
        out={'height':7,'width':w,'target':w+11,'status':'SAT' if sat else 'UNSAT' if complete else 'unknown',
             'solver':solver,'cores':records,'search_order':order,'results':results,
             'known_crop_bounds':BOUNDS,'total_cap_seconds':total,'per_core_cap_seconds':each,
             'wall_seconds':time.monotonic()-begin,
             'source_sha256':{name:hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                              for name in ('seven_row_deficit_one_complement_sat.py','fixed_excess_eleven_sat.py',
                                           'fixed_row_core_sat.py','seven_row_equality_sat.py')}}
        destination.write_text(json.dumps(out,indent=2)+'\n');return out
    for index in order:
        remaining=total-time.monotonic()+begin
        if remaining<=0:break
        cap=min(each,remaining);receive,send=mp.Pipe(duplex=False)
        child=mp.Process(target=worker,args=(send,w,index,solver));start=time.monotonic()
        child.start();send.close();result=None;info=None
        def accept(event):
            nonlocal result,info
            if event['event']=='encoded':info=event['info']
            elif event['event']=='result':result=event
            elif event['event']=='error':result={'index':index,'status':'error',**event}
        while child.is_alive() and time.monotonic()-start<cap:
            try:
                if receive.poll(min(1,max(0,cap-time.monotonic()+start))):accept(receive.recv())
            except (EOFError,OSError):break
        if child.is_alive():child.terminate()
        child.join(5)
        while True:
            try:
                if not receive.poll():break
                accept(receive.recv())
            except (EOFError,OSError):break
        receive.close()
        if result is None:result={'index':index,'status':'unknown','seconds':time.monotonic()-start,'info':info}
        results.append(result);save()
        print(json.dumps({k:v for k,v in result.items() if k not in ('info','stats')}),flush=True)
        if result['status'] in ('SAT','error'):break
    out=save()
    print(json.dumps({k:v for k,v in out.items() if k not in ('cores','search_order','results','source_sha256')}),flush=True)


if __name__=='__main__':mp.freeze_support();main()
