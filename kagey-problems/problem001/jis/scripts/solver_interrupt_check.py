"""Does Solver.interrupt() stop solve_limited() for each pysat backend?

Each backend is run in its own child process on a pigeonhole instance (13
pigeons, 12 holes) with a threading.Timer that calls interrupt() after 1.5 s;
the parent kills the child after 40 s and records whether it returned.

Usage: python solver_interrupt_check.py OUT.json        (parent)
       python solver_interrupt_check.py child SOLVER     (child, internal)
"""
import json
import subprocess
import sys
import threading
import time
from itertools import combinations


def pigeonhole(p, h):
    v = lambda i, j: i * h + j + 1
    cnf = [[v(i, j) for j in range(h)] for i in range(p)]
    for j in range(h):
        for i1, i2 in combinations(range(p), 2):
            cnf.append([-v(i1, j), -v(i2, j)])
    return cnf


def child(name):
    from pysat.solvers import Solver
    s = Solver(name=name, bootstrap_with=pigeonhole(13, 12))
    timer = threading.Timer(1.5, s.interrupt)
    t0 = time.time()
    timer.start()
    r = s.solve_limited(expect_interrupt=True)
    timer.cancel()
    print(json.dumps({'solver': name, 'returned': repr(r), 'seconds': round(time.time() - t0, 2)}))


def main():
    out = sys.argv[1]
    results = []
    for name in ('cadical153', 'cadical195', 'glucose4', 'glucose42', 'minisat22', 'maplechrono', 'lingeling'):
        t0 = time.time()
        try:
            cp = subprocess.run([sys.executable, __file__, 'child', name], capture_output=True, text=True, timeout=40)
            line = cp.stdout.strip().splitlines()[-1] if cp.stdout.strip() else ''
            try:
                rec = json.loads(line)
            except Exception:
                rec = {'solver': name, 'returned': 'error', 'stderr': cp.stderr[-500:]}
            rec['honours_interrupt'] = rec.get('returned') == 'None'
        except subprocess.TimeoutExpired:
            rec = {'solver': name, 'returned': 'did not return within 40 s; child killed',
                   'seconds': round(time.time() - t0, 1), 'honours_interrupt': False}
        print(rec, flush=True)
        results.append(rec)
    json.dump({'instance': 'pigeonhole 13 pigeons 12 holes', 'interrupt_after_seconds': 1.5,
               'kill_after_seconds': 40, 'results': results}, open(out, 'w'), indent=1)


if __name__ == '__main__':
    if sys.argv[1] == 'child':
        child(sys.argv[2])
    else:
        main()
