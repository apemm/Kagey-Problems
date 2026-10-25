"""Run the check scripts of Paper F with the current interpreter.

verify_identities.py checks the exact identities of Section 2 (and the renewal identities and the
inversion used in Sections 5 and 6) by brute force in exact arithmetic. verify_coefficient.py checks
the coefficient C(j) of Theorem thm:second-order, Table tab:antimode and the constant of Theorem
thm:mode(d). verify_preparation.py checks Theorem thm:preparation(c), (d) and Corollary
cor:stationary on three initial runs. verify_bigjump.py checks the numbers of Remark
rem:no-single-formula. verify_modes.py checks the numbers of Section sec:extrema. certify_atlas.py computes the exact law at N = 5000 behind Figure 1(a), with
the a priori error bound and the ball-arithmetic comparison at N = 600, and certify_antimode.py
certifies the antimodes of Figure 1(b) and Table tab:antimode.

The default is the quick run, which takes about half a minute. It runs the five verify scripts
and reads the certificates in data/ (the outputs of the certify scripts) through
verify_coefficient.py. Add --full to rerun the two certify scripts first, which takes about two
minutes in all, most of it the antimode at N = 8000. The figure script figures/make_atlas_figure.py is
not run. Needs numpy, scipy, mpmath and python-flint. Each script writes its output with its sha256
and the date to data/, and this runner writes its summary to data/verify_all_output.txt (or
data/verify_all_output_full.txt with --full).
"""
from datetime import date
from pathlib import Path
import argparse
import hashlib
import platform
import subprocess
import sys
import time

base = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
mode = parser.add_mutually_exclusive_group()
mode.add_argument('--quick', action='store_true', help='quick run (the default)')
mode.add_argument('--full', action='store_true', help='also rerun the two certify scripts')
args = parser.parse_args()
scripts = ['verify_identities.py',    # Section 2, eq:cover etc., thm:inverse(a), exact arithmetic
           'verify_coefficient.py',   # thm:second-order, tab:antimode, eq:second-renewal, thm:mode(d)
           'verify_preparation.py',   # thm:preparation(c), (d), cor:stationary
           'verify_bigjump.py',       # rem:no-single-formula
           'verify_modes.py']         # sec:extrema
if args.full:
    # the certificates first, so that verify_coefficient.py reads the fresh data/antimode.json
    scripts = ['certify_atlas.py',    # Figure 1(a), eq:run-recursion, ball check at N = 600
               'certify_antimode.py'] + scripts
start = time.time()
failed = []
times = []
for name in scripts:
    print(f'\n=== Running {name}', flush=True)
    t0 = time.time()
    result = subprocess.run([sys.executable, '-I', '-B', str(base / name)], cwd=base)
    times.append((name, time.time() - t0, result.returncode))
    if result.returncode:
        failed.append(name)
summary = []
for name, dt, rc in times:
    summary.append(f'{"PASS" if rc == 0 else "FAIL"}  {name}  ({dt:.1f} s)  '
                   f'sha256 {hashlib.sha256((base / name).read_bytes()).hexdigest()}')
minutes = (time.time() - start) / 60
if failed:
    summary.append(f'{len(failed)} of {len(scripts)} scripts reported failures: {", ".join(failed)} '
                   f'({minutes:.1f} min).')
else:
    summary.append(f'All {len(scripts)} scripts passed ({minutes:.1f} min).')
print('\n=== Summary', flush=True)
print('\n'.join(summary), flush=True)
header = ['# script: verify_all.py' + (' --full' if args.full else ''),
          f'# sha256: {hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}',
          f'# date: {date.today().isoformat()}',
          f'# python {platform.python_version()}',
          '# the output of each script is in data/ (verify_*_output.txt, atlas_N5000.json, antimode.json)', '']
out = base / 'data' / ('verify_all_output_full.txt' if args.full else 'verify_all_output.txt')
out.write_text('\n'.join(header + summary) + '\n', encoding='utf-8')
sys.exit(1 if failed else 0)
