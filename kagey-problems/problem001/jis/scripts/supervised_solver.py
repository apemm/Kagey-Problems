"""A pysat solver that runs in a separate worker process, with deadlines enforced by the parent.

Solver.interrupt() does not stop CaDiCaL 1.5.3 or 1.9.5 inside pysat (see
solver_interrupt_check.py and data/cells_check/solver_interrupt_check.json), so a
threading.Timer cap does not bound a CaDiCaL call. Here the solver lives in a worker process.
solve_limited(timeout=...) waits for the answer at most `timeout` seconds of wall time; when the
deadline passes, the parent kills the worker and the call returns None, which the scripts record
as "unresolved". The killed solver cannot be used again (solve_limited returns None and
get_model returns None from then on). An exception in the worker (for example an unknown solver
name) is raised in the parent as WorkerError, so a broken backend is never read as UNSAT.

The interface is the part of pysat.solvers.Solver the scripts use:
    with SupervisedSolver(name, bootstrap_with=clauses) as s:
        r = s.solve_limited(timeout=60)       # True, False, or None at the deadline
        model = s.get_model()
        s.add_clause([...])
"""
import multiprocessing
import time
import traceback

CHUNK = 50000


class WorkerError(RuntimeError):
    pass


def _worker(conn, name):
    try:
        from pysat.solvers import Solver
        solver = Solver(name=name)
    except BaseException:
        conn.send(('error', traceback.format_exc()))
        return
    conn.send(('ready', None))
    pending_error = None
    while True:
        try:
            cmd, arg = conn.recv()
        except EOFError:
            break
        try:
            if cmd == 'add':
                if pending_error is None:
                    solver.append_formula(arg)
                continue
            if pending_error is not None:
                conn.send(('error', pending_error))
                continue
            if cmd == 'solve':
                conn.send(('ok', solver.solve(assumptions=arg)))
            elif cmd == 'sync':
                conn.send(('ok', None))
            elif cmd == 'model':
                conn.send(('ok', solver.get_model()))
            elif cmd == 'close':
                solver.delete()
                conn.send(('ok', None))
                break
        except BaseException:
            if cmd == 'add':
                pending_error = traceback.format_exc()
            else:
                conn.send(('error', traceback.format_exc()))


class SupervisedSolver:
    def __init__(self, name, bootstrap_with=None):
        ctx = multiprocessing.get_context('spawn')
        self._conn, child = ctx.Pipe()
        self._proc = ctx.Process(target=_worker, args=(child, name), daemon=True)
        self._proc.start()
        child.close()
        self.name = name
        self.killed = False
        self._reply()
        if bootstrap_with:
            self.append_formula(bootstrap_with)
            # wait until the worker has loaded the formula, so that a deadline counts
            # solving time only, as the timer of the earlier version did
            self._conn.send(('sync', None))
            self._reply()

    def _reply(self):
        try:
            kind, value = self._conn.recv()
        except EOFError:
            raise WorkerError('solver worker for %s ended without an answer' % self.name)
        if kind == 'error':
            self._kill()
            raise WorkerError('solver worker for %s failed:\n%s' % (self.name, value))
        return value

    def _kill(self):
        if self._proc.is_alive():
            self._proc.kill()
        self._proc.join()
        self.killed = True

    def append_formula(self, clauses):
        clauses = [list(c) for c in clauses]
        for i in range(0, len(clauses), CHUNK):
            self._conn.send(('add', clauses[i:i + CHUNK]))

    def add_clause(self, clause):
        if not self.killed:
            self._conn.send(('add', [list(clause)]))

    def solve_limited(self, timeout, assumptions=()):
        """True or False, or None when the deadline passed (the worker is then killed)."""
        if self.killed:
            return None
        self._conn.send(('solve', list(assumptions)))
        if not self._conn.poll(max(0.0, timeout)):
            self._kill()
            return None
        return self._reply()

    def get_model(self):
        if self.killed:
            return None
        self._conn.send(('model', None))
        return self._reply()

    def delete(self):
        if not self.killed and self._proc.is_alive():
            try:
                self._conn.send(('close', None))
                if self._conn.poll(10):
                    self._conn.recv()
            except (EOFError, OSError, BrokenPipeError):
                pass
            self._proc.join(5)
        if self._proc.is_alive():
            self._kill()
        self.killed = True
        self._conn.close()

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.delete()
        return False


def solve_with_deadline(name, clauses, cap):
    """One call with a wall-clock cap. Returns (status, model, seconds); status is SAT, UNSAT
    or unresolved (deadline reached, worker killed)."""
    t0 = time.time()
    with SupervisedSolver(name, bootstrap_with=clauses) as s:
        r = s.solve_limited(timeout=cap)
        model = s.get_model() if r else None
    status = 'SAT' if r else ('UNSAT' if r is False else 'unresolved')
    return status, model, time.time() - t0
