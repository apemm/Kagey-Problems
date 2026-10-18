"""Check that every stored result of the cells_sat_check.py and six_row_sat_check.py batches was
written by the child process of that batch.

The batch opens OUT.json.log for writing when it starts the child, so the log holds the output of
that child only. The child prints its result line (the JSON record without the witness) as its
last action, after writing OUT.json. For each job of a jobs file this script compares the last
line of the log with OUT.json (status, solver, clause and variable counts, encode and solve
seconds). A match shows that OUT.json was written by the child of that batch run and that the
child finished. A job killed at the cap has an empty log and an "unresolved" record.

Usage (from kagey-problems/problem001):
    python jis/scripts/batch_log_check.py jis/data/cells_check/sat_jobs.json \
        jis/data/cells_check/sat_jobs_satcases.json jis/data/cells_check/ssat_jobs.json
Prints one line per jobs file and every job that does not match; exits 1 if any SAT or UNSAT
record lacks a matching log line.
"""
import json
import os
import sys

KEYS = ['status', 'solver', 'clauses', 'variables', 'encode_seconds', 'solve_seconds']


def check_job(out):
    with open(out) as fh:
        rec = json.load(fh)
    log = out + '.log'
    if not os.path.exists(log):
        return rec.get('status'), 'no log'
    with open(log) as fh:
        lines = [line for line in fh.read().splitlines() if line.strip()]
    if not lines:
        return rec.get('status'), 'empty log'
    try:
        last = json.loads(lines[-1])
    except ValueError:
        return rec.get('status'), 'last log line is not a result line'
    if all(last.get(k) == rec.get(k) for k in KEYS):
        return rec.get('status'), 'log matches'
    return rec.get('status'), 'log differs: %s' % {k: (last.get(k), rec.get(k)) for k in KEYS}


def main(paths):
    bad = 0
    for jobs_path in paths:
        with open(jobs_path) as fh:
            jobs = json.load(fh)
        matched = 0
        for job in jobs:
            out = job[4] if len(job) == 6 else job[3]
            status, verdict = check_job(out)
            if verdict == 'log matches':
                matched += 1
                continue
            if status in ('SAT', 'UNSAT'):
                bad += 1
            print('   ', os.path.basename(out), status, verdict)
        print('%s: %d jobs, %d with a matching log line' % (jobs_path, len(jobs), matched))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
