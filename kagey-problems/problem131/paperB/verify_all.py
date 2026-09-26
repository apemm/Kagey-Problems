"""Run the checks for Paper B of Problem 131 with the current interpreter.

The default (--quick) takes about 2 minutes. Paper B has 1 long script that runs only with
--full. verify_B_tie_repair.py takes about 3 minutes (dynamic programs over all bins at N = 300
and N = 1002) and rewrites data/B_tie_repair_output.txt. verify_general_start.py (about 20 s) and
verify_crossover_factor.py (about 50 s, then its repair mode in under 1 s) always run. The scripts
use only the standard library.

verify_general_start.py and verify_B_tie_repair.py report their checks in their output rather than
through the exit code, so that output must be read (it is also saved in data/). Some of their lines
show failures on purpose, since they belong to the 2 registered predictions that failed, T1(e) and
T4 (see data/ledger_B_tie.md). So their output cannot be judged by searching for "False". The
other scripts stop with a nonzero exit code when a check fails, and then this runner stops too.
predict_general_start.py and verify_crossover_factor.py predict only evaluate formulas for the
registered predictions and check nothing, so this runner does not run them.

Every script runs in this folder. Several of them rewrite their recorded output in data/. With
--dry-run the commands are printed and nothing is run. From the Problem 131 folder,
python -B verify_all.py --paper b calls this runner.
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
                  help='also run the long script (about 3 minutes more)')
parser.add_argument('--dry-run', action='store_true',
                    help='print the commands in order and run nothing')
args = parser.parse_args()

# Each entry is a script name followed by its arguments.
runs = [(name,) for name in ('verify_geometry.py', 'verify_simplex_threshold.py',
                             'verify_frontier_boundary.py', 'verify_frontier_modes.py',
                             'verify_vertex_completion.py', 'verify_general_start.py')]
runs += [('verify_crossover_factor.py',), ('verify_crossover_factor.py', 'repair')]
long_runs = [('verify_B_tie_repair.py',)]
if args.full:
    runs += long_runs
else:
    print('Skipping verify_B_tie_repair.py (about 3 min). Add --full to run it.', flush=True)

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
    print(f'\nAll {len(runs)} runs of Paper B finished with exit code 0. Read the output of the '
          'scripts that report their checks there (see the docstring of verify_all.py).',
          flush=True)
