"""Tests for supervised_solver.py: a deadline stops CaDiCaL, whose Solver.interrupt() is
ignored, and the call is recorded as unresolved. Run with python -m pytest jis/tests or
directly with python jis/tests/test_supervised_solver.py.
"""
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPTS = os.path.abspath(os.path.join(HERE, '..', 'scripts'))
sys.path.insert(0, SCRIPTS)

from pysat.examples.genhard import PHP  # noqa: E402

from supervised_solver import SupervisedSolver, WorkerError, solve_with_deadline  # noqa: E402

HARD = PHP(12).clauses          # 13 pigeons, 12 holes: far beyond a two-second cap


def test_deadline_stops_cadical():
    for name in ('cadical153', 'cadical195', 'glucose4'):
        t0 = time.time()
        status, model, seconds = solve_with_deadline(name, HARD, 2)
        assert status == 'unresolved' and model is None, (name, status)
        assert time.time() - t0 < 20, (name, time.time() - t0)


def test_small_instances_are_answered():
    status, model, _ = solve_with_deadline('cadical195', [[1, 2], [-1]], 30)
    assert status == 'SAT' and 2 in model and -1 in model
    status, model, _ = solve_with_deadline('cadical153', [[1, 2], [-1, 2], [1, -2], [-1, -2]], 30)
    assert status == 'UNSAT' and model is None


def test_incremental_enumeration():
    with SupervisedSolver('cadical153', bootstrap_with=[[1, 2]]) as s:
        n = 0
        while s.solve_limited(timeout=30):
            n += 1
            s.add_clause([-lit for lit in s.get_model()])
    assert n == 3


def test_broken_backend_raises():
    try:
        solve_with_deadline('not-a-solver', [[1]], 30)
    except WorkerError:
        return
    raise AssertionError('an unknown solver name must raise, not return a status')


def test_small_cells_sat_records_timeout_as_unresolved():
    import small_cells_sat
    status, model, _ = small_cells_sat.solve_capped('cadical153', HARD, cap=2)
    assert status == 'unresolved' and model is None


def test_six_row_structured_sat_records_timeout_as_unresolved():
    import six_row_structured_sat
    status, model, _ = six_row_structured_sat.solve_capped('cadical153', HARD, 2)
    assert status == 'unresolved' and model is None


if __name__ == '__main__':
    for name, fn in sorted(globals().items()):
        if name.startswith('test_') and callable(fn):
            fn()
            print('passed', name, flush=True)
