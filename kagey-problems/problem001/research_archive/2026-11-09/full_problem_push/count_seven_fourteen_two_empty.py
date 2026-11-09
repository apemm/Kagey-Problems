"""Count the nineteen full-K3,4 cores with twelve doubles and two empties.

This is the additional width-fourteen excess-ten family absent at width thirteen.
It leaves the existing counting shards and their encoder source unchanged.
"""
from itertools import combinations
from pathlib import Path
import hashlib
import json
import multiprocessing as mp
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / ".runtime"))


def reflect(core):
    return tuple(sorted(sum(1 << (6-r) for r in range(7) if mask >> r & 1)
                        for mask in core))


def catalog():
    all_cores = set()
    for left in combinations(range(7), 3):
        left = set(left)
        core = tuple(sorted((1 << a) | (1 << b)
                            for a in left for b in range(7) if b not in left))
        all_cores.add(core)
    assert len(all_cores) == 35
    representatives = sorted({min(core, reflect(core)) for core in all_cores})
    assert len(representatives) == 19
    return representatives


def encode_two_empty(core, rects, flags):
    from fixed_row_core_sat import encode
    from pysat.card import CardEnc, EncType
    w = 14
    record = {"masks": list(core), "empty_columns": 1}
    clauses, info = encode(w, record, rects, flags,
                          known_bounds={9:17, 10:18, 11:20, 12:21, 13:23})
    # The base encoder has one empty type and exactly-once constraints for it.
    # Keep that same type, replacing only its occurrence cardinality.
    htypes = 8 + len(core)
    empty_vars = [7*w + htypes*c + 1 for c in range(w)]
    obsolete = {tuple(empty_vars)}
    obsolete.update((-empty_vars[c], -empty_vars[d])
                    for c, d in combinations(range(w), 2))
    removed = [clause for clause in clauses if tuple(clause) in obsolete]
    assert len(removed) == 1 + w*(w-1)//2
    assert {tuple(clause) for clause in removed} == obsolete
    clauses = [clause for clause in clauses if tuple(clause) not in obsolete]
    count = CardEnc.equals(empty_vars, bound=2, top_id=info["variables"],
                           encoding=EncType.totalizer)
    clauses += count.clauses
    info.update(variables=count.nv, clauses=len(clauses),
                replaced_empty_cardinality=[1,2], removed_empty_clauses=len(removed))
    return clauses, info


def worker(send, index, core):
    try:
        from pysat.solvers import Solver
        from fixed_row_core_sat import rectangles, axis_rectangles, collision
        rects = rectangles(7, 14)
        axis = set(axis_rectangles(7, 14))
        clauses, info = encode_two_empty(core, rects, [r not in axis for r in rects])
        send.send({"event":"encoded", "info":info})
        vertical = 1 if reflect(core) == core else 2
        models = []
        with Solver(name="cadical195", bootstrap_with=clauses) as solver:
            while solver.solve():
                true = {v for v in solver.get_model() if v > 0}
                cells = [p for p in range(98) if p+1 in true]
                black = sum(1 << p for p in cells)
                columns = [sum(1 << r for r in range(7)
                               if black >> (14*r+c) & 1) for c in range(14)]
                assert len(cells) == 24 and columns.count(0) == 2
                assert sorted(v for v in columns if v) == list(core)
                assert columns.index(core[0]) < 7
                assert collision(rects, black) is None
                models.append(hex(black))
                solver.add_clause([-p-1 for p in cells])
            send.send({"event":"result", "status":"complete", "index":index,
                       "models":models, "vertical_weight":vertical,
                       "horizontal_weight":2, "weighted_count":len(models)*2*vertical,
                       "stats":solver.accum_stats()})
    except BaseException:
        send.send({"event":"result", "status":"error", "index":index,
                   "traceback":traceback.format_exc()})
    finally:
        send.close()


def main():
    per_core = float(sys.argv[1]) if len(sys.argv)>1 else 60
    total_cap = float(sys.argv[2]) if len(sys.argv)>2 else 1800
    cores = catalog()
    source_paths = [Path(__file__), HERE/"fixed_row_core_sat.py",
                    HERE/"seven_row_equality_sat.py", HERE.parents[2]/"verify_narrow.py"]
    manifest = {"width":14, "target":24, "core_count":len(cores),
                "cores":[list(c) for c in cores], "empty_columns":2,
                "source_sha256":{str(p.relative_to(HERE)) if p.is_relative_to(HERE)
                    else str(p):hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in source_paths}}
    (HERE/"seven_fourteen_two_empty_manifest.json").write_text(
        json.dumps(manifest, indent=2)+"\n")
    output = HERE/"seven_fourteen_two_empty_count.jsonl"
    complete = {}
    if output.exists():
        for line in output.read_text().splitlines():
            item = json.loads(line)
            if item["status"] == "complete":
                complete[item["index"]] = item
    began = time.monotonic()
    for index, core in enumerate(cores):
        if index in complete:
            continue
        if time.monotonic()-began >= total_cap:
            break
        receiver, sender = mp.Pipe(duplex=False)
        child = mp.Process(target=worker, args=(sender,index,core))
        child.start();sender.close()
        started = time.monotonic();result = None;info = None
        while child.is_alive() and time.monotonic()-started < per_core:
            try:
                if receiver.poll(.25):
                    event = receiver.recv()
                    if event["event"] == "encoded":
                        info = event["info"]
                    elif event["event"] == "result":
                        result = event
                        break
            except (EOFError,OSError):
                break
        if child.is_alive():
            child.terminate()
        child.join(5)
        while result is None:
            try:
                if not receiver.poll():
                    break
                event = receiver.recv()
                if event["event"] == "result":
                    result = event
            except (EOFError,OSError):
                break
        receiver.close()
        if result is None:
            result = {"status":"timeout", "index":index}
        result.update(info=info, seconds=time.monotonic()-started,
                      source_sha256=manifest["source_sha256"])
        with output.open("a", encoding="utf-8") as stream:
            stream.write(json.dumps(result,separators=(",",":"))+"\n")
        if result["status"] == "complete":
            complete[index] = result
        print(json.dumps({"index":index,"status":result["status"],
              "models":len(result.get("models",[])),
              "weighted_count":result.get("weighted_count"),
              "seconds":result["seconds"]}),flush=True)
    summary = {"complete":len(complete)==19, "completed_indices":sorted(complete),
               "weighted_count":sum(x["weighted_count"] for x in complete.values()),
               "seconds":time.monotonic()-began}
    (HERE/"seven_fourteen_two_empty_summary.json").write_text(
        json.dumps(summary,indent=2)+"\n")
    print(json.dumps(summary),flush=True)


if __name__ == "__main__":
    mp.freeze_support()
    main()
