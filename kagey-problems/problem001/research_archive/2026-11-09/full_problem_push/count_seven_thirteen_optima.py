"""Bounded projected enumeration of the three remaining optimal row cores.

Only black point assignments are counted. Cardinality is fixed at23, so a
negative clause on one complete black set blocks exactly that point assignment.
"""
from pathlib import Path
import json
import multiprocessing as mp
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'.runtime'))
from fixed_row_core_sat import encode,rectangles,axis_rectangles,collision


def reflected(core):
    return sorted(sum(1 << (6-r) for r in range(7) if mask >> r & 1) for mask in core)


def worker(send,indices,model_cap,geometry):
    try:
        from pysat.solvers import Solver
        encoder = encode
        if geometry == 'fiber':
            from fiber_fixed_core_encoding import encode as encoder
        records = json.loads((HERE/'fixed_excess_ten_cores.json').read_text())['cores']
        w = 13
        rects = rectangles(7,w)
        axis = set(axis_rectangles(7,w))
        flags = [r not in axis for r in rects]
        for index in indices:
            record = records[index]
            assert max(x.bit_count() for x in record['masks']) == 3
            assert record['empty_columns'] == 0
            assert record['masks'] != reflected(record['masks'])
            clauses,info = encoder(w,record,rects,flags,
                                   known_bounds={9:17,10:18,11:20,12:21})
            send.send(dict(event='starting',index=index,info=info))
            seen = set()
            began = time.monotonic()
            with Solver(name='cadical195',bootstrap_with=clauses) as solver:
                while solver.solve():
                    true = {x for x in solver.get_model() if x > 0}
                    cells = [p for p in range(7*w) if p+1 in true]
                    black = sum(1 << p for p in cells)
                    assert len(cells) == 23 and black not in seen
                    assert collision(rects,black) is None
                    seen.add(black)
                    columns = [sum(1 << r for r in range(7) if black >> (r*w+c) & 1)
                               for c in range(w)]
                    assert sorted(x for x in columns if x.bit_count() >= 2) == record['masks']
                    anchor = columns.index(record['masks'][0])
                    assert anchor <= w//2
                    weight = 1 if anchor == w//2 else 2
                    send.send(dict(event='model',index=index,black_hex=hex(black),
                                   anchor_column=anchor+1,horizontal_weight=weight))
                    solver.add_clause([-p-1 for p in cells])
                    if len(seen) >= model_cap:
                        send.send(dict(event='model_cap',index=index,count=len(seen)))
                        return
            send.send(dict(event='complete_core',index=index,models=len(seen),
                           seconds=time.monotonic()-began))
        send.send(dict(event='complete'))
    except BaseException:
        send.send(dict(event='error',traceback=traceback.format_exc()))
    finally:
        send.close()


def main():
    cap = float(sys.argv[1]) if len(sys.argv)>1 else 180
    model_cap = int(sys.argv[2]) if len(sys.argv)>2 else 5000
    geometry = sys.argv[3] if len(sys.argv)>3 else 'compact'
    assert geometry in ('compact','fiber')
    indices = [996,998,999]
    receive,send = mp.Pipe(duplex=False)
    process = mp.Process(target=worker,args=(send,indices,model_cap,geometry))
    began = time.monotonic()
    process.start()
    send.close()
    models = []
    completed = []
    error = None
    complete = False
    reason = 'time cap'
    def accept(event):
        nonlocal error,complete,reason
        kind = event['event']
        if kind == 'model':
            models.append(event)
            if len(models)%100 == 0:
                print(json.dumps(dict(event='progress',models=len(models),index=event['index'])),flush=True)
        elif kind == 'complete_core':
            completed.append(event)
            print(json.dumps(event),flush=True)
        elif kind == 'complete':
            complete = True
            reason = 'complete'
        elif kind == 'model_cap':
            reason = 'model cap'
        elif kind == 'error':
            error = event['traceback']
            reason = 'error'
    while process.is_alive() and time.monotonic()-began < cap:
        try:
            if receive.poll(min(1,max(0,cap-time.monotonic()+began))):
                accept(receive.recv())
        except (EOFError,OSError):
            break
    if process.is_alive():
        process.terminate()
    process.join(5)
    while True:
        try:
            if not receive.poll():
                break
            accept(receive.recv())
        except (EOFError,OSError):
            break
    totals = {i:sum(2*r['horizontal_weight'] for r in models if r['index']==i)
              for i in indices}
    out = dict(height=7,width=13,target=23,indices=indices,geometry=geometry,
               status='complete' if complete and not error else reason,
               completed_cores=completed,projected_models=len(models),
               weighted_counts_by_core=totals,
               exact_optimum_count=sum(totals.values()) if complete and not error else None,
               cap_seconds=cap,model_cap=model_cap,wall_seconds=time.monotonic()-began,
               models=models,error=error)
    (HERE/f'seven_thirteen_optimum_count_{geometry}.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='models'}),flush=True)


if __name__ == '__main__':
    mp.freeze_support()
    main()
