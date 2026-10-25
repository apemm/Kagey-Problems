"""Run the checks of Paper C2 (problem131_reconstruction.tex) and save their outputs under data/.

Each script runs in its own process as `<python> -I <script>`, in this folder. Its output goes to
data/<script>_output.txt, behind a header with the sha256 of the script, the date, the versions of
Python and of the packages, the run time and the exit status. A script passes when every
assertion in it holds, which is when it exits with status 0.

The five scripts run in a few minutes on a laptop. Needs numpy, scipy, sympy and mpmath.
Run:  py -I verify_all.py [--only NAME ...]
"""
import argparse
import datetime
import hashlib
import platform
import subprocess
import sys
import time
from pathlib import Path

BASE = Path(__file__).resolve().parent
SCRIPTS = (
    # (script, what it checks)
    ('verify_reconstruction.py', 'the identifiability and reconstruction theorems'),
    ('verify_finite_horizon.py', 'the finite-horizon entry times'),
    ('verify_threshold.py', 'the least admissible horizon of the design'),
    ('verify_cycles.py', 'the two Arrhenius examples, in exact arithmetic'),
    ('verify_attraction.py', 'the calibrated attraction design'),
)


def versions():
    out = [f'Python {platform.python_version()}']
    for mod in ('numpy', 'scipy', 'sympy', 'mpmath'):
        try:
            out.append(f'{mod} {__import__(mod).__version__}')
        except ImportError:
            out.append(f'{mod} missing')
    return ', '.join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--only', nargs='*', help='run only these scripts')
    args = parser.parse_args()
    (BASE / 'data').mkdir(exist_ok=True)
    vers = versions()
    results = []
    t_all = time.time()
    for name, what in SCRIPTS:
        if args.only and name not in args.only:
            continue
        path = BASE / name
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        cmd = [sys.executable, '-I', str(path)]
        print(f'Running {name} ({what})', flush=True)
        t0 = time.time()
        proc = subprocess.run(cmd, cwd=BASE, capture_output=True, text=True, encoding='utf-8', errors='replace')
        dt = time.time() - t0
        status = 'PASS' if proc.returncode == 0 else f'FAIL (exit status {proc.returncode})'
        header = [f'# script: {name}',
                  f'# sha256: {digest}',
                  f'# checks: {what}',
                  f'# command: py -I {name}',
                  f'# date: {datetime.datetime.now().isoformat(timespec="seconds")}',
                  f'# software: {vers}',
                  f'# run time: {dt:.0f} s',
                  f'# result: {status}',
                  '']
        out = BASE / 'data' / (path.stem + '_output.txt')
        out.write_text('\n'.join(header) + proc.stdout + ('\n# stderr:\n' + proc.stderr if proc.stderr else ''),
                       encoding='utf-8')
        print(f'  {status} in {dt:.0f} s, output in data/{out.name}', flush=True)
        results.append((name, status, dt))
    print()
    for name, status, dt in results:
        print(f'{name:28s} {status:6s} {dt:7.0f} s')
    bad = [r for r in results if r[1] != 'PASS']
    print(f'\n{len(results) - len(bad)} of {len(results)} scripts passed ({time.time() - t_all:.0f} s).')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
