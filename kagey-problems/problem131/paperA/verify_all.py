"""Run the checks for Paper A of Problem 131 with the current interpreter.

The default (--quick) takes about 2 minutes. Paper A has 2 long scripts that run only with
--full. verify_every_n.py takes about 8 minutes and rewrites data/every_n_certificates.csv and
data/every_n_output.txt, and verify_every_n_sign.py takes about 13 minutes. Both run before
verify_every_n_guards.py, which reads the certificate file. Without --full the guards read the
certificate file that is already in data/. The scripts use only the standard library.

verify_every_n_sign.py, verify_every_n_guards.py, verify_uniform_llt.py and
verify_uniform_llt_cor5.py report their checks in their output rather than through the exit code,
so that output must be read (it is also saved in data/). The other scripts stop with a nonzero exit
code when a check fails, and then this runner stops too.

Every script runs in this folder. Several of them rewrite their recorded output in data/. With
--dry-run the commands are printed and nothing is run. From the Problem 131 folder,
python -B verify_all.py --paper a calls this runner.
"""
from pathlib import Path
import argparse
import subprocess
import sys

base = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
mode = parser.add_mutually_exclusive_group()
mode.add_argument('--quick', action='store_true', help='the default')
mode.add_argument('--full', action='store_true',
                  help='also run the 2 long scripts (about 21 minutes more)')
parser.add_argument('--dry-run', action='store_true',
                    help='print the commands in order and run nothing')
args = parser.parse_args()

# Each entry is a script name followed by its arguments.
runs = [('verify.py',), ('check_bessel.py',), ('verify_adjacent.py',),
        ('verify_allbin.py',), ('verify_periodic_window.py',),
        ('verify_every_n_guards.py',),
        ('verify_uniform_llt.py',), ('verify_uniform_llt.py', '--run2'),
        ('verify_uniform_llt.py', '--run3'), ('verify_uniform_llt_cor5.py',)]
long_runs = [('verify_every_n.py',), ('verify_every_n_sign.py',)]
if args.full:
    at = runs.index(('verify_every_n_guards.py',))
    runs[at:at] = long_runs
else:
    print('Skipping verify_every_n.py (about 8 min) and verify_every_n_sign.py (about 13 min). '
          'Add --full to run them.', flush=True)

if args.dry_run:
    print(f'Commands, in order, run in {base}:')
for run in runs:
    label = ' '.join(run)
    if args.dry_run:
        print(f'  python -B {label}')
        continue
    print(f'\nRunning {label}', flush=True)
    result = subprocess.run([sys.executable, '-B', str(base / run[0]), *run[1:]], cwd=base)
    if result.returncode:
        sys.exit(result.returncode)
if not args.dry_run:
    print(f'\nAll {len(runs)} runs of Paper A finished with exit code 0. Read the output of the '
          'scripts that report their checks there (see the docstring of verify_all.py).',
          flush=True)
