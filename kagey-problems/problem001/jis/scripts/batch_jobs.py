"""Shared batch runner for cells_sat_check.py and six_row_sat_check.py.

A batch runs every job in its own child process and accepts a child result only when all of
the following hold:

  * the child exited with return code 0 before the cap;
  * the child wrote a fresh attempt file, at a path that did not exist when the child was
    started and whose name carries the job key;
  * the attempt file is complete JSON whose job key, parameters and input hashes equal the
    ones the parent computed for the job, and whose status is SAT or UNSAT;
  * the job-specific check passes (for SAT, the stored witness is valid and has the size
    asked for).

The job key is the SHA-256 of the driver name, the job parameters and the SHA-256 of every
script the child imports from this folder. An accepted attempt is published by an atomic
rename onto the job's output path. A rejected or failed job publishes an "error" record, and
a job killed at the cap publishes an "unresolved" record, both atomically, so an old file at
the output path is never read back as the result of the new run. A batch refuses to start, with
exit code 3 and no file written, when the output path of some job already exists, unless it is
called with overwrite=True (the --overwrite flag of the drivers). So a failed rerun cannot
replace a stored evidence file by accident.

The summary JOBS_summary.json records every job with its status, and the batch exits with
code 0 only when every job ended SAT or UNSAT: code 1 if some job ended in error, code 2 if
no job failed but some job was killed at the cap.
"""
import hashlib
import json
import os
import subprocess
import sys
import time
import uuid

HERE = os.path.dirname(os.path.abspath(__file__))
RESOLVED = ('SAT', 'UNSAT')


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for block in iter(lambda: fh.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def input_hashes(names):
    """SHA-256 of the given script files of this folder, by file name."""
    return {name: sha256_file(os.path.join(HERE, name)) for name in names}


def job_key(driver, params, inputs):
    blob = json.dumps({'driver': driver, 'params': params, 'inputs': inputs}, sort_keys=True)
    return hashlib.sha256(blob.encode('utf-8')).hexdigest()


def atomic_write_json(path, obj):
    """Write JSON to a temporary file in the same folder, then rename it onto path."""
    folder = os.path.dirname(os.path.abspath(path))
    tmp = os.path.join(folder, '.%s.%s.tmp' % (os.path.basename(path), uuid.uuid4().hex))
    with open(tmp, 'w') as fh:
        json.dump(obj, fh, indent=1)
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, path)


def pop_job_key(argv):
    """Remove an optional --job-key=KEY argument from argv and return KEY (or None)."""
    key = None
    rest = []
    for a in argv:
        if a.startswith('--job-key='):
            key = a.split('=', 1)[1]
        else:
            rest.append(a)
    argv[:] = rest
    return key


def check_attempt(path, key, params, inputs, extra_check):
    """Return (status, reason). status is SAT or UNSAT when the attempt is accepted."""
    try:
        with open(path) as fh:
            res = json.load(fh)
    except FileNotFoundError:
        return 'error', 'child exited 0 but wrote no attempt file'
    except Exception as exc:
        return 'error', 'attempt file unreadable: %s' % exc
    if not isinstance(res, dict):
        return 'error', 'attempt file is not a JSON object'
    if res.get('job_key') != key:
        return 'error', 'job key mismatch'
    if res.get('complete') is not True:
        return 'error', 'attempt not marked complete'
    if res.get('input_sha256') != inputs:
        return 'error', 'input hashes changed during the run'
    for name, value in params.items():
        if res.get(name) != value:
            return 'error', 'parameter %s mismatch: %r != %r' % (name, res.get(name), value)
    status = res.get('status')
    if status not in RESOLVED:
        return 'error', 'status %r is neither SAT nor UNSAT' % (status,)
    problem = extra_check(res)
    if problem:
        return 'error', problem
    return status, 'accepted'


def batch_args(argv):
    """Parse BATCH JOBS.json CONCURRENCY CAP_SECONDS [--overwrite] into (jobs, conc, cap, overwrite)."""
    overwrite = '--overwrite' in argv
    rest = [a for a in argv if a != '--overwrite']
    return rest[1], int(rest[2]), float(rest[3]), overwrite


def run_batch(driver, jobs_path, concurrency, cap, describe, input_names, extra_check,
              poll=0.2, overwrite=False):
    """describe(job) -> (params dict, out path, arguments before and after the output path).

    The child is called as  python SCRIPT run BEFORE... ATTEMPT_PATH AFTER... --job-key=KEY
    and must write its result atomically to ATTEMPT_PATH with the fields job_key,
    input_sha256, complete and the parameters in params."""
    script = os.path.join(HERE, driver)
    with open(jobs_path) as fh:
        jobs = json.load(fh)
    existing = [describe(job)[1] for job in jobs if os.path.exists(describe(job)[1])]
    if existing and not overwrite:
        for path in existing:
            print('output path exists, refusing to start without --overwrite:', path,
                  flush=True)
        return 3
    inputs = input_hashes(input_names)
    pending = list(jobs)
    running = []
    summary = []
    while pending or running:
        while pending and len(running) < concurrency:
            job = pending.pop(0)
            params, out, before, after = describe(job)
            key = job_key(driver, params, inputs)
            attempt = '%s.attempt-%s-%s.json' % (out, key[:16], uuid.uuid4().hex[:8])
            if os.path.exists(attempt):
                raise RuntimeError('attempt path already exists: %s' % attempt)
            log = open(out + '.log', 'w')
            cmd = ([sys.executable, script, 'run'] + [str(a) for a in before] + [attempt]
                   + [str(a) for a in after] + ['--job-key=' + key])
            p = subprocess.Popen(cmd, stdout=log, stderr=subprocess.STDOUT)
            running.append(dict(job=job, params=params, out=out, key=key, attempt=attempt,
                                proc=p, start=time.time(), log=log))
        time.sleep(poll)
        still = []
        for r in running:
            rc = r['proc'].poll()
            elapsed = round(time.time() - r['start'], 1)
            if rc is None and elapsed <= cap:
                still.append(r)
                continue
            if rc is None:
                r['proc'].kill()
                r['proc'].wait()
                status, reason = 'unresolved', 'process killed at the cap'
            elif rc != 0:
                status, reason = 'error', 'child exited with return code %s' % rc
            else:
                status, reason = check_attempt(r['attempt'], r['key'], r['params'], inputs,
                                               extra_check)
            r['log'].close()
            if status in RESOLVED:
                os.replace(r['attempt'], r['out'])
            else:
                if os.path.exists(r['attempt']):
                    os.remove(r['attempt'])
                record = dict(r['params'])
                record.update({'status': status, 'reason': reason, 'job_key': r['key'],
                               'input_sha256': inputs, 'return_code': rc, 'cap_seconds': cap,
                               'wall_seconds': elapsed})
                atomic_write_json(r['out'], record)
            summary.append([r['job'], status, elapsed, reason])
            print(status, r['job'], elapsed, reason, flush=True)
        running = still
    errors = sum(row[1] == 'error' for row in summary)
    unresolved = sum(row[1] == 'unresolved' for row in summary)
    code = 1 if errors else (2 if unresolved else 0)
    root, _ = os.path.splitext(jobs_path)
    atomic_write_json(root + '_summary.json', {
        'driver': driver, 'cap_seconds': cap, 'concurrency': concurrency,
        'input_sha256': inputs, 'jobs': summary, 'errors': errors, 'unresolved': unresolved,
        'all_resolved': code == 0, 'exit_code': code,
        'timing': 'wall_seconds per job: wall time of the child process, polled every %s s'
                  % poll})
    return code
