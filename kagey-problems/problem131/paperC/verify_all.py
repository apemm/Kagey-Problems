"""Run the checks of Paper C1 (problem131_chains.tex) and save their outputs under data/.

The checks of the identifiability results (reconstruction, finite horizons, low temperature)
moved with those results to the companion paper in ../paperC2 on October 24, 2026.

Each script runs in its own process as `<python> -I <script>`, in this folder. Its output goes to
data/<script>_output.txt, behind a header with the sha256 of the script, the date, the versions of
Python and of the packages, the run time and the exit status. A script passes when every
assertion in it holds, which is when it exits with status 0.

The default runs in about nine minutes on a laptop. With --full
the three older scripts that have heavy cells also run those (the directed 3-cycle at N = 10^8,
the whole 4-cycle in the continuum, C_5 at N = 72, the path P_4 at N = 150 and 300, the census of
graphs on 6 states, and the cells at N = 160 of the first-order section), which adds a few hours,
and verify_layer_general.py adds S = 64.
Needs numpy, scipy, sympy and mpmath. Run:  py -I verify_all.py [--full] [--only NAME ...]

The script verify_sticky_fisher.py in this folder checks the notes ../S3_sticky_note and
../S1_endpoint_information_note, not this paper, and is not run here.
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
    # (script, takes --full, what it checks)
    ('verify_first_order.py', True, 'the exact law, the continuum density, the rate and first-order selection'),
    ('verify_second_order.py', True, 'the local law, the constants, the crossings and the tie windows'),
    ('verify_forest.py', False, 'the tree formula for K_F on every face'),
    ('verify_rate_flows.py', False, 'the rate through flows'),
    ('verify_weak_field.py', False, 'a weak field'),
    ('verify_examples.py', True, 'the winners on complete graphs, cycles and small graphs, finite-N modes'),
    ('verify_layer.py', False, 'the boundary layer'),
    ('verify_layer_general.py', True, 'the weighted facet chain on two facets with four states'),
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
    parser.add_argument('--full', action='store_true', help='also run the heavy cells')
    parser.add_argument('--quick', action='store_true',
                        help='the default run; accepted so that ../verify_all.py can pass it')
    parser.add_argument('--only', nargs='*', help='run only these scripts')
    args = parser.parse_args()
    (BASE / 'data').mkdir(exist_ok=True)
    vers = versions()
    results = []
    t_all = time.time()
    for name, has_full, what in SCRIPTS:
        if args.only and name not in args.only:
            continue
        path = BASE / name
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        cmd = [sys.executable, '-I', str(path)] + (['--full'] if args.full and has_full else [])
        print(f'Running {name} ({what})', flush=True)
        t0 = time.time()
        proc = subprocess.run(cmd, cwd=BASE, capture_output=True, text=True, encoding='utf-8', errors='replace')
        dt = time.time() - t0
        status = 'PASS' if proc.returncode == 0 else f'FAIL (exit status {proc.returncode})'
        header = [f'# script: {name}',
                  f'# sha256: {digest}',
                  f'# checks: {what}',
                  f'# command: py -I {name}' + (' --full' if args.full and has_full else ''),
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
