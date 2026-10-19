"""Solve each CNF with CaDiCaL (text LRAT), then check the proof with lrat-check and the Lean
checker. One solver and one checker run at a time. Results append to results.jsonl.

The work folder (UNSAT_WORK, default the current folder) holds cnf/, proofs/, logs/, and the two
checkers at bin/lrat-check.exe and lean/.lake/build/bin/lratcheck.exe. The solver is CADICAL
(default cadical on the PATH). SOLVE_CAP and CHECK_CAP are the caps in seconds. A proof over
50 MB is gzipped after both checkers accept it. Peak memory is read with psutil (peak_wset,
Windows only).

Usage: python pipeline.py NAME_GLOB [NAME_GLOB ...]   (names of files in cnf/, without .cnf)
"""
import fnmatch
import glob
import gzip
import hashlib
import json
import os
import queue
import shutil
import subprocess
import sys
import threading
import time

import psutil

W = os.path.abspath(os.environ.get('UNSAT_WORK', os.getcwd()))
CAD = os.environ.get('CADICAL', 'cadical')
LRATCHECK = os.path.join(W, 'bin', 'lrat-check.exe')
LEANCHECK = os.path.join(W, 'lean', '.lake', 'build', 'bin', 'lratcheck.exe')
SOLVE_CAP = int(os.environ.get('SOLVE_CAP', 7200))
CHECK_CAP = int(os.environ.get('CHECK_CAP', 7200))
LOCK = threading.Lock()


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for chunk in iter(lambda: fh.read(1 << 22), b''):
            h.update(chunk)
    return h.hexdigest()


def run(cmd, log, cap):
    """Run cmd with output to log; return (exit code or None if capped, seconds, peak MB)."""
    t0 = time.time()
    with open(log, 'w') as fh:
        p = subprocess.Popen(cmd, stdout=fh, stderr=subprocess.STDOUT)
        ps = psutil.Process(p.pid)
        peak = 0
        while p.poll() is None:
            try:
                peak = max(peak, ps.memory_info().peak_wset)
            except Exception:
                pass
            if time.time() - t0 > cap:
                p.kill()
                p.wait()
                return None, round(time.time() - t0, 1), round(peak / 2 ** 20)
            time.sleep(0.2)
    return p.returncode, round(time.time() - t0, 1), round(peak / 2 ** 20)


def record(rec):
    with LOCK:
        with open(os.path.join(W, 'results.jsonl'), 'a') as fh:
            fh.write(json.dumps(rec) + '\n')
    print(json.dumps(rec), flush=True)


def solve(name):
    cnf = os.path.join(W, 'cnf', name + '.cnf')
    proof = os.path.join(W, 'proofs', name + '.lrat')
    code, sec, peak = run([CAD, '--lrat', '--binary=false', cnf, proof],
                          os.path.join(W, 'logs', name + '.cadical.log'), SOLVE_CAP)
    status = {20: 'UNSAT', 10: 'SAT', None: 'CAPPED'}.get(code, f'exit {code}')
    return {'name': name, 'step': 'solve', 'solver': 'cadical 2.1.2', 'status': status,
            'seconds': sec, 'peak_mb': peak, 'cap_seconds': SOLVE_CAP,
            'cnf_sha256': sha256(cnf)}


def free_mb():
    return psutil.virtual_memory().available / 2 ** 20


def check(name):
    cnf = os.path.join(W, 'cnf', name + '.cnf')
    proof = os.path.join(W, 'proofs', name + '.lrat')
    size = os.path.getsize(proof)
    rec = {'name': name, 'step': 'check', 'proof_bytes': size, 'proof_sha256': sha256(proof)}
    log1 = os.path.join(W, 'logs', name + '.lratcheck.log')
    code, sec, peak = run([LRATCHECK, cnf, proof], log1, CHECK_CAP)
    text = open(log1, errors='replace').read()
    ok = code == 0 and '\nc VERIFIED' in '\n' + text and 'FAILED' not in text
    rec['lrat_check'] = {'verified': ok, 'exit': code, 'seconds': sec, 'peak_mb': peak}
    need = 7 * size / 2 ** 20 + 1500
    while free_mb() < need:
        time.sleep(30)
    rt = os.path.join(W, 'logs', name + '.roundtrip.cnf')
    log2 = os.path.join(W, 'logs', name + '.lean.log')
    code, sec, peak = run([LEANCHECK, cnf, proof, rt], log2, CHECK_CAP)
    text = open(log2, errors='replace').read()
    ok2 = code == 0 and 's VERIFIED' in text
    body = b''.join(l for l in open(cnf, 'rb') if not l.startswith(b'c'))
    same = os.path.exists(rt) and open(rt, 'rb').read() == body
    if same:
        os.remove(rt)
    rec['lean_check'] = {'verified': ok2, 'exit': code, 'seconds': sec, 'peak_mb': peak,
                         'parse_roundtrip_identical': same}
    if ok and ok2 and size > 50 * 2 ** 20:
        with open(proof, 'rb') as src, gzip.open(proof + '.gz', 'wb', compresslevel=6) as dst:
            shutil.copyfileobj(src, dst, 1 << 22)
        os.remove(proof)
        rec['stored'] = name + '.lrat.gz'
    else:
        rec['stored'] = name + '.lrat'
    return rec


def main():
    names = sorted(os.path.basename(p)[:-4] for p in glob.glob(os.path.join(W, 'cnf', '*.cnf')))
    todo = [n for n in names if any(fnmatch.fnmatch(n, g) for g in sys.argv[1:])]
    order = {g: i for i, g in enumerate(sys.argv[1:])}
    todo.sort(key=lambda n: (min(order[g] for g in sys.argv[1:] if fnmatch.fnmatch(n, g)), n))
    q = queue.Queue()

    def checker():
        while True:
            n = q.get()
            if n is None:
                return
            try:
                record(check(n))
            except Exception as e:
                record({'name': n, 'step': 'check', 'error': repr(e)})

    th = threading.Thread(target=checker)
    th.start()
    for n in todo:
        if os.path.exists(os.path.join(W, 'proofs', n + '.lrat')) and \
                os.path.exists(os.path.join(W, 'logs', n + '.cadical.log')) and \
                's UNSATISFIABLE' in open(os.path.join(W, 'logs', n + '.cadical.log')).read():
            rec = {'name': n, 'step': 'solve', 'status': 'UNSAT', 'reused_proof': True}
            record(rec)
            q.put(n)
            continue
        rec = solve(n)
        record(rec)
        if rec['status'] == 'UNSAT':
            q.put(n)
    q.put(None)
    th.join()


if __name__ == '__main__':
    main()
