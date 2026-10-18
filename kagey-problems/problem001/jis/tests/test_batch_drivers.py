"""Regression tests for the batch drivers cells_sat_check.py and six_row_sat_check.py.

A failed child must never be summarized as SAT or UNSAT, whether or not an old output file
exists at its output path, and the batch must then exit nonzero. Run with
    python -m pytest jis/tests          (from kagey-problems/problem001)
or directly with
    python jis/tests/test_batch_drivers.py
Every test writes only into a fresh temporary folder.
"""
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPTS = os.path.abspath(os.path.join(HERE, '..', 'scripts'))
sys.path.insert(0, SCRIPTS)

import batch_jobs  # noqa: E402

SEED = {'status': 'UNSAT', 'note': 'planted test fixture, not a solver result'}


def _job(kind, out, solver, rows=2, cols=2, bound=1):
    if kind == 'cells':
        return [rows, cols, bound, solver, out, None]
    return [2, 0, solver, out]


def _run_batch(kind, jobs, folder, cap=60, overwrite=True):
    jobs_path = os.path.join(folder, kind + '_jobs.json')
    with open(jobs_path, 'w') as fh:
        json.dump(jobs, fh)
    script = os.path.join(SCRIPTS, kind + '_sat_check.py')
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    cmd = [sys.executable, '-B', script, 'batch', jobs_path, '3', str(cap)]
    p = subprocess.run(cmd + (['--overwrite'] if overwrite else []),
                       capture_output=True, text=True, timeout=300, env=env)
    if not overwrite and p.returncode == 3:
        return p.returncode, None
    with open(os.path.join(folder, kind + '_jobs_summary.json')) as fh:
        summary = json.load(fh)
    return p.returncode, summary


def _failed_child_controls(kind):
    with tempfile.TemporaryDirectory() as folder:
        seeded = os.path.join(folder, kind + '_seeded.json')
        clean = os.path.join(folder, kind + '_clean.json')
        good = os.path.join(folder, kind + '_good.json')
        with open(seeded, 'w') as fh:
            json.dump(SEED, fh)
        jobs = [_job(kind, seeded, 'not-a-solver'), _job(kind, clean, 'not-a-solver'),
                _job(kind, good, 'glucose3')]
        code, summary = _run_batch(kind, jobs, folder)
        status = {row[0][-2 if kind == 'cells' else -1]: row[1] for row in summary['jobs']}
        # both failed children end as error, never SAT or UNSAT
        assert status[seeded] == 'error', status
        assert status[clean] == 'error', status
        # the planted file is replaced by an error record, not read back as a result
        with open(seeded) as fh:
            assert json.load(fh)['status'] == 'error'
        with open(clean) as fh:
            assert json.load(fh)['status'] == 'error'
        # the working backend still gives the known answer (2 x 2 is SAT, the six-row
        # width-2 instance is UNSAT)
        assert status[good] == ('SAT' if kind == 'cells' else 'UNSAT'), status
        with open(good) as fh:
            res = json.load(fh)
        assert res['complete'] is True and res['job_key'] and res['input_sha256']
        # the aggregate fails
        assert code == 1 and summary['exit_code'] == 1 and not summary['all_resolved']
        assert summary['errors'] == 2
        # no attempt or temporary file is left behind
        left = [f for f in os.listdir(folder) if '.attempt-' in f or f.endswith('.tmp')]
        assert not left, left


def test_cells_failed_children_are_errors():
    _failed_child_controls('cells')


def test_six_row_failed_children_are_errors():
    _failed_child_controls('six_row')


def test_existing_output_refused_without_overwrite():
    for kind in ('cells', 'six_row'):
        with tempfile.TemporaryDirectory() as folder:
            seeded = os.path.join(folder, kind + '_seeded.json')
            with open(seeded, 'w') as fh:
                json.dump(SEED, fh)
            code, summary = _run_batch(kind, [_job(kind, seeded, 'not-a-solver')], folder,
                                       overwrite=False)
            assert code == 3 and summary is None
            # the stored file is untouched and no summary or log is written
            with open(seeded) as fh:
                assert json.load(fh) == SEED
            assert sorted(os.listdir(folder)) == sorted([kind + '_jobs.json',
                                                         kind + '_seeded.json'])


def test_cells_good_batch_succeeds():
    with tempfile.TemporaryDirectory() as folder:
        out = os.path.join(folder, 'good.json')
        code, summary = _run_batch('cells', [_job('cells', out, 'glucose3')], folder)
        assert code == 0 and summary['all_resolved'] and summary['jobs'][0][1] == 'SAT'


def test_cells_job_killed_at_cap_is_unresolved():
    with tempfile.TemporaryDirectory() as folder:
        out = os.path.join(folder, 'slow.json')
        with open(out, 'w') as fh:
            json.dump(SEED, fh)
        # 7 x 7 with at least 15 points does not finish within one second
        job = _job('cells', out, 'cadical195', rows=7, cols=7, bound=15)
        code, summary = _run_batch('cells', [job], folder, cap=1)
        assert summary['jobs'][0][1] == 'unresolved', summary
        assert code == 2 and not summary['all_resolved']
        with open(out) as fh:
            assert json.load(fh)['status'] == 'unresolved'


def test_attempt_checks_reject_mismatches():
    params = {'rows': 2, 'cols': 2, 'bound': 1, 'rowcase': None, 'solver': 'glucose3'}
    inputs = {'a.py': '0' * 64}
    key = batch_jobs.job_key('cells_sat_check.py', params, inputs)
    good = dict(params, status='UNSAT', job_key=key, input_sha256=inputs, complete=True)
    cases = {
        'accepted': good,
        'job key mismatch': dict(good, job_key='f' * 64),
        'attempt not marked complete': dict(good, complete=False),
        'input hashes changed during the run': dict(good, input_sha256={'a.py': '1' * 64}),
        'parameter bound mismatch': dict(good, bound=2),
        'neither SAT nor UNSAT': dict(good, status='unresolved'),
    }
    with tempfile.TemporaryDirectory() as folder:
        path = os.path.join(folder, 'attempt.json')
        status, reason = batch_jobs.check_attempt(path, key, params, inputs, lambda r: None)
        assert status == 'error' and 'no attempt file' in reason
        for expect, record in cases.items():
            batch_jobs.atomic_write_json(path, record)
            status, reason = batch_jobs.check_attempt(path, key, params, inputs,
                                                      lambda r: None)
            if expect == 'accepted':
                assert status == 'UNSAT' and reason == 'accepted'
            else:
                assert status == 'error' and expect in reason, (expect, reason)
        with open(path, 'w') as fh:
            fh.write('{"status": "UNS')
        status, reason = batch_jobs.check_attempt(path, key, params, inputs, lambda r: None)
        assert status == 'error' and 'unreadable' in reason


if __name__ == '__main__':
    for name, fn in sorted(globals().items()):
        if name.startswith('test_') and callable(fn):
            fn()
            print('passed', name, flush=True)
