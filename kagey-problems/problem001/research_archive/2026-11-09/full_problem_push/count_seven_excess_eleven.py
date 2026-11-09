"""Resumable projected enumeration over the complete excess-eleven catalog."""
from pathlib import Path
import argparse
import json
import multiprocessing as mp
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / ".runtime"))
BOUNDS = {9:17, 10:18, 11:20, 12:21, 13:23, 14:24, 15:25,
          16:26, 17:27, 18:29, 19:30}


def worker(send, width, index, record, model_cap):
    try:
        from pysat.solvers import Solver
        from fixed_row_core_sat import encode, rectangles, axis_rectangles, collision
        rects = rectangles(7, width)
        axis = set(axis_rectangles(7, width))
        clauses, info = encode(width, record, rects, [r not in axis for r in rects],
                               known_bounds=BOUNDS)
        send.send(dict(event="encoded", info=info))
        reflected = sorted(sum(1 << (6-r) for r in range(7) if mask >> r & 1)
                           for mask in record["masks"])
        vertical_weight = 1 if reflected == record["masks"] else 2
        models, weighted = [], 0
        start = time.monotonic()
        with Solver(name="cadical195", bootstrap_with=clauses) as solver:
            while solver.solve():
                true = {v for v in solver.get_model() if v > 0}
                cells = [p for p in range(7*width) if p+1 in true]
                black = sum(1 << p for p in cells)
                assert len(cells) == width+11 and collision(rects, black) is None
                columns = [sum(1 << r for r in range(7)
                               if black >> (r*width+c) & 1) for c in range(width)]
                assert sorted(v for v in columns if v.bit_count() >= 2) == record["masks"]
                assert columns.count(0) == record["empty_columns"]
                anchor = columns.index(record["masks"][0])
                assert anchor < (width+1)//2
                horizontal_weight = 1 if width % 2 and anchor == width//2 else 2
                weighted += horizontal_weight * vertical_weight
                models.append(hex(black))
                solver.add_clause([-p-1 for p in cells])
                if len(models) >= model_cap:
                    send.send(dict(event="result", status="model_cap", models=models,
                                   weighted_count=weighted, vertical_weight=vertical_weight,
                                   seconds=time.monotonic()-start))
                    return
            send.send(dict(event="result", status="complete", models=models,
                           weighted_count=weighted, vertical_weight=vertical_weight,
                           seconds=time.monotonic()-start, solver_stats=solver.accum_stats()))
    except BaseException:
        send.send(dict(event="result", status="error", traceback=traceback.format_exc()))
    finally:
        send.close()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--width", type=int, default=20)
    parser.add_argument("--per-core", type=float, default=120)
    parser.add_argument("--seconds", type=float, default=7200)
    parser.add_argument("--model-cap", type=int, default=20000)
    parser.add_argument("--indices")
    parser.add_argument("--tag", default="")
    args = parser.parse_args()
    assert 18 <= args.width <= 20
    from fixed_excess_eleven_sat import catalog
    records = catalog()
    indices = (list(range(len(records))) if args.indices is None
               else list(map(int, args.indices.split(","))))
    suffix = f"_{args.tag}" if args.tag else ""
    path = HERE / f"excess_eleven_count_w{args.width}{suffix}.jsonl"
    done = set()
    if path.exists():
        done = {r["index"] for r in map(json.loads, path.read_text().splitlines())
                if r["status"] == "complete"}
    begin = time.monotonic()
    for index in indices:
        if index in done:
            continue
        if time.monotonic()-begin >= args.seconds:
            break
        receive, send = mp.Pipe(duplex=False)
        child = mp.Process(target=worker,
                           args=(send, args.width, index, records[index], args.model_cap))
        child.start()
        send.close()
        start = time.monotonic()
        info, result = None, None
        while child.is_alive() and time.monotonic()-start < args.per_core:
            try:
                if receive.poll(.25):
                    event = receive.recv()
                    if event["event"] == "encoded":
                        info = event["info"]
                    elif event["event"] == "result":
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
                if event["event"] == "result":
                    result = event
            except (EOFError, OSError):
                break
        receive.close()
        if result is None:
            result = dict(status="timeout")
        result.update(index=index, width=args.width, target=args.width+11,
                      core=records[index], info=info,
                      wall_seconds=time.monotonic()-start)
        with path.open("a", encoding="utf-8") as out:
            out.write(json.dumps(result, separators=(",", ":"))+"\n")
        print(json.dumps({k:v for k,v in result.items()
                          if k not in ("models", "core", "info")}), flush=True)
    print(json.dumps(dict(event="finished", seconds=time.monotonic()-begin)), flush=True)


if __name__ == "__main__":
    mp.freeze_support()
    main()
