"""Resumable bounded projected counts for the complete excess-ten core catalog."""
from pathlib import Path
import argparse
import json
import multiprocessing as mp
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / '.runtime'))


def worker(send, width, index, record, model_cap):
    try:
        from pysat.solvers import Solver
        from fixed_row_core_sat import encode, rectangles, axis_rectangles, collision
        rects = rectangles(7, width)
        axis = set(axis_rectangles(7, width))
        flags = [r not in axis for r in rects]
        clauses, info = encode(width, record, rects, flags,
            known_bounds={9:17, 10:18, 11:20, 12:21, 13:23})
        send.send({'event':'encoded', 'info':info})
        models = []
        reflected = sorted(sum(1 << (6-r) for r in range(7) if mask >> r & 1)
                           for mask in record['masks'])
        vertical_weight = 1 if reflected == record['masks'] else 2
        weighted_count = 0
        began = time.monotonic()
        with Solver(name='cadical195', bootstrap_with=clauses) as solver:
            while solver.solve():
                true = {v for v in solver.get_model() if v > 0}
                cells = [p for p in range(7*width) if p+1 in true]
                black = sum(1 << p for p in cells)
                assert len(cells) == width+10
                assert collision(rects, black) is None
                columns = [sum(1 << r for r in range(7)
                               if black >> (r*width+c) & 1) for c in range(width)]
                assert sorted(v for v in columns if v.bit_count() >= 2) == record['masks']
                assert columns.count(0) == record['empty_columns']
                anchor = columns.index(record['masks'][0])
                assert anchor < (width+1)//2
                horizontal_weight = 1 if width % 2 and anchor == width//2 else 2
                weighted_count += vertical_weight * horizontal_weight
                models.append(hex(black))
                solver.add_clause([-p-1 for p in cells])
                if len(models) >= model_cap:
                    send.send(dict(event='result', status='model_cap', index=index,
                        models=models, weighted_count=weighted_count,
                        vertical_weight=vertical_weight, seconds=time.monotonic()-began))
                    return
            send.send(dict(event='result', status='complete', index=index,
                models=models, weighted_count=weighted_count,
                vertical_weight=vertical_weight, seconds=time.monotonic()-began,
                solver_stats=solver.accum_stats()))
    except BaseException:
        send.send(dict(event='result', status='error', index=index,
                       traceback=traceback.format_exc()))
    finally:
        send.close()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--width', type=int, default=14)
    parser.add_argument('--shard', type=int, default=0)
    parser.add_argument('--shards', type=int, default=2)
    parser.add_argument('--per-core', type=float, default=30)
    parser.add_argument('--seconds', type=float, default=7200)
    parser.add_argument('--model-cap', type=int, default=20000)
    parser.add_argument('--indices', help='Optional comma-separated indices for a bounded follow-up')
    args = parser.parse_args()
    assert args.width >= 13 and 0 <= args.shard < args.shards
    records = json.loads((HERE / 'fixed_excess_ten_cores.json').read_text())['cores']
    indices = (list(map(int,args.indices.split(','))) if args.indices else
               list(range(args.shard, len(records), args.shards)))
    suffix = '_followup' if args.indices else ''
    path = HERE / f'excess_ten_count_w{args.width}_shard{args.shard}{suffix}.jsonl'
    done = set()
    if path.exists():
        for line in path.read_text().splitlines():
            record = json.loads(line)
            if record.get('status') == 'complete':
                done.add(record['index'])
    began = time.monotonic()
    completed = 0
    unknown = []
    total = 0
    for index in indices:
        if index in done:
            continue
        if time.monotonic()-began >= args.seconds:
            break
        receive, send = mp.Pipe(duplex=False)
        child = mp.Process(target=worker,
            args=(send,args.width,index,records[index],args.model_cap))
        child.start()
        send.close()
        core_started = time.monotonic()
        info = None
        result = None
        while child.is_alive() and time.monotonic()-core_started < args.per_core:
            try:
                if receive.poll(.25):
                    event = receive.recv()
                    if event['event'] == 'encoded':
                        info = event['info']
                    elif event['event'] == 'result':
                        result = event
                        break
            except (EOFError, OSError):
                break
        if child.is_alive():
            child.terminate()
        child.join(5)
        while result is None:
            try:
                if not receive.poll():
                    break
                event = receive.recv()
                if event['event'] == 'result':
                    result = event
            except (EOFError,OSError):
                break
        receive.close()
        if result is None:
            result = dict(status='timeout', index=index)
        result.update(width=args.width, target=args.width+10,
                      wall_seconds=time.monotonic()-core_started, info=info)
        with path.open('a', encoding='utf-8') as out:
            out.write(json.dumps(result, separators=(',',':'))+'\n')
            out.flush()
        if result['status'] == 'complete':
            completed += 1
            total += result['weighted_count']
        else:
            unknown.append(index)
        if completed % 25 == 0 or result['status'] != 'complete' or result.get('models'):
            print(json.dumps(dict(index=index, status=result['status'],
                  models=len(result.get('models',[])), weighted=result.get('weighted_count'),
                  completed=completed, unknown=len(unknown), subtotal=total,
                  elapsed=time.monotonic()-began)), flush=True)
    print(json.dumps(dict(event='finished', path=str(path), completed=completed,
                         unknown=unknown, subtotal=total,
                         elapsed=time.monotonic()-began)), flush=True)


if __name__ == '__main__':
    mp.freeze_support()
    main()
