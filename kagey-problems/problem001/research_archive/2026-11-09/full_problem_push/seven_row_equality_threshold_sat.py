"""Bounded complete-core equality search, with final-graph window bounds."""
from itertools import combinations
from pathlib import Path
import hashlib
import json
import multiprocessing as mp
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / '.runtime'))
from fixed_row_core_sat import encode, rectangles, axis_rectangles, collision

BOUNDS = {9: 17, 10: 18, 11: 20, 12: 21, 13: 22, 14: 23}


def catalog():
    def reflected(mask):
        return sum(1 << (6-r) for r in range(7) if mask >> r & 1)
    cores = set()
    for part in combinations(range(7), 3):
        other = set(range(7)) - set(part)
        core = tuple(sorted((1 << a) | (1 << b) for a in part for b in other))
        cores.add(min(core, tuple(sorted(map(reflected, core)))))
    assert len(cores) == 19
    return [{'masks': list(core), 'empty_columns': 0} for core in sorted(cores)]


def worker(send, w, index, solver_name):
    try:
        from pysat.solvers import Solver
        begun = time.monotonic()
        record = catalog()[index]
        rects = rectangles(7, w)
        axis = set(axis_rectangles(7, w))
        clauses, info = encode(w, record, rects, [r not in axis for r in rects],
                               known_bounds=BOUNDS, axis_graph=set(record['masks']))
        send.send({'event': 'encoded', 'info': info, 'seconds': time.monotonic()-begun})
        with Solver(name=solver_name, bootstrap_with=clauses) as solver:
            sat = solver.solve()
            result = {'event': 'result', 'index': index, 'status': 'SAT' if sat else 'UNSAT',
                      'seconds': time.monotonic()-begun, 'info': info,
                      'stats': solver.accum_stats()}
            if sat:
                model = set(solver.get_model())
                black = sum(1 << p for p in range(7*w) if p+1 in model)
                assert black.bit_count() == w+12 and collision(rects, black) is None
                result['black_hex'] = hex(black)
                result['column_word'] = ','.join(''.join(str(r+1) for r in range(7)
                                              if black >> (r*w+c) & 1) for c in range(w))
                result['presentations_checked'] = len(rects)
            send.send(result)
    except BaseException:
        send.send({'event': 'error', 'traceback': traceback.format_exc()})
    finally:
        send.close()


def main():
    w = int(sys.argv[1]); assert w >= 17
    start = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    end = int(sys.argv[3]) if len(sys.argv) > 3 else 19
    per_core = float(sys.argv[4]) if len(sys.argv) > 4 else 45
    solver = sys.argv[5] if len(sys.argv) > 5 else 'cadical195'
    assert 0 <= start < end <= 19
    begin = time.monotonic(); results = []
    output = HERE / f'equality_h7_w{w}_{start}_{end}_{solver}.json'
    sources = ['seven_row_equality_threshold_sat.py', 'fixed_row_core_sat.py',
               'seven_row_equality_sat.py']
    def save():
        sat = any(r['status'] == 'SAT' for r in results)
        complete = len(results) == end-start and all(r['status'] == 'UNSAT' for r in results)
        out = {'height': 7, 'width': w, 'target': w+12, 'start_index': start,
               'end_exclusive': end, 'per_core_seconds': per_core, 'solver': solver,
               'status': 'SAT' if sat else 'UNSAT_range' if complete else 'unknown',
               'wall_seconds': time.monotonic()-begin, 'cores': catalog(),
               'crop_black_bounds': BOUNDS, 'results': results,
               'source_sha256': {name: hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                                 for name in sources}}
        output.write_text(json.dumps(out, indent=2)+'\n')
        return out
    for index in range(start, end):
        receive, send = mp.Pipe(duplex=False)
        child = mp.Process(target=worker, args=(send, w, index, solver))
        began = time.monotonic(); child.start(); send.close(); result = None; info = None
        while child.is_alive() and time.monotonic()-began < per_core:
            try:
                if receive.poll(min(1, max(0, per_core-time.monotonic()+began))):
                    event = receive.recv()
                    if event['event'] == 'encoded': info = event
                    elif event['event'] == 'result': result = event
                    else: result = {'index': index, 'status': 'error', **event}
            except (EOFError, OSError): break
        if child.is_alive(): child.terminate()
        child.join(5)
        while True:
            try:
                if not receive.poll(): break
                event = receive.recv()
                if event['event'] == 'result': result = event
                elif event['event'] == 'error': result = {'index': index, 'status': 'error', **event}
            except (EOFError, OSError): break
        receive.close()
        if result is None:
            result = {'index': index, 'status': 'unknown', 'seconds': time.monotonic()-began,
                      'encoding': info}
        results.append(result); save()
        print(json.dumps({k: v for k, v in result.items() if k not in ('info', 'stats', 'encoding')}), flush=True)
        if result['status'] in ('SAT', 'error'): break
    out = save()
    print(json.dumps({k: v for k, v in out.items() if k not in ('cores', 'results', 'source_sha256')}), flush=True)


if __name__ == '__main__':
    mp.freeze_support(); main()
