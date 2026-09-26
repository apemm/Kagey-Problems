"""Run the checks for Papers A to D of Problem 131 with the current interpreter.

Paper A has 2 long scripts that run only with --full. verify_every_n.py takes about 8 minutes and
rewrites data/every_n_certificates.csv and data/every_n_output.txt, and verify_every_n_sign.py
takes about 13 minutes. Both run before verify_every_n_guards.py, which reads the certificate
file. Without --full the guards read the certificate file that is already in data/.

Paper B has 1 long script that runs only with --full. verify_B_tie_repair.py takes about 3
minutes (dynamic programs over all bins at N = 300 and N = 1002) and rewrites
data/B_tie_repair_output.txt. verify_general_start.py (about 20 s) and verify_crossover_factor.py
(about 50 s, then its repair mode in under 1 s) always run.

Papers C and D have their own runners, paperC/verify_all.py and paperD/verify_all.py. This script
calls them with --quick, or with --full when --full is given. The quick runs take a few minutes
each. With --full, Paper C takes up to about half an hour and Paper D about 45 minutes. If the
folder paperC or paperD is missing, this script says so in one line and goes on. The scripts of
Papers A and B use only the standard library. Those of Papers C and D need numpy, scipy and mpmath,
and Paper C also needs sympy.

verify_every_n_sign.py, verify_every_n_guards.py, verify_uniform_llt.py,
verify_uniform_llt_cor5.py, verify_general_start.py and verify_B_tie_repair.py report their checks
in their output rather than through the exit code, so that output must be read (it is also saved
in data/). Some lines of the last 2 show failures on purpose, since they belong to the 2
registered predictions that failed, T1(e) and T4 (see data/ledger_B_tie.md). So their output
cannot be judged by searching for "False". The other scripts, and the runners of Papers C and D,
stop with a nonzero exit code when a check fails, and then this runner stops too.

Several scripts rewrite their recorded output in data/. With --dry-run the commands are printed
and nothing is run.
"""
from pathlib import Path
import argparse
import subprocess
import sys

base = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
parser.add_argument('--paper', choices=('a', 'b', 'c', 'd', 'all'), default='all')
parser.add_argument('--full', action='store_true',
                    help='also run the 2 long Paper A scripts (about 21 minutes more), the '
                         'long Paper B script (about 3 minutes more) and the heavy cells of '
                         'Papers C and D')
parser.add_argument('--dry-run', action='store_true',
                    help='print the commands in order and run nothing')
args = parser.parse_args()

# Paper A: each entry is a script name followed by its arguments.
paper_a = [('verify.py',), ('check_bessel.py',), ('verify_adjacent.py',),
           ('verify_allbin.py',), ('verify_periodic_window.py',),
           ('verify_every_n_guards.py',),
           ('verify_uniform_llt.py',), ('verify_uniform_llt.py', '--run2'),
           ('verify_uniform_llt.py', '--run3'), ('verify_uniform_llt_cor5.py',)]
paper_a_long = [('verify_every_n.py',), ('verify_every_n_sign.py',)]
if args.full:
    at = paper_a.index(('verify_every_n_guards.py',))
    paper_a[at:at] = paper_a_long

paper_b = ('verify_geometry.py', 'verify_simplex_threshold.py',
           'verify_frontier_boundary.py', 'verify_frontier_modes.py',
           'verify_vertex_completion.py', 'verify_general_start.py')
paper_b = [(name,) for name in paper_b]
paper_b += [('verify_crossover_factor.py',), ('verify_crossover_factor.py', 'repair')]
paper_b_long = [('verify_B_tie_repair.py',)]
if args.full:
    paper_b += paper_b_long

# Papers C and D: one call of the paper's own runner, run in its folder.
mode = '--full' if args.full else '--quick'
delegated = {'c': 'paperC', 'd': 'paperD'}

papers = 'abcd' if args.paper == 'all' else args.paper
runs = []          # (folder, script and arguments)
for paper in papers:
    if paper == 'a':
        runs += [(base, run) for run in paper_a]
    elif paper == 'b':
        runs += [(base, run) for run in paper_b]
    else:
        folder = base / delegated[paper]
        if (folder / 'verify_all.py').is_file():
            runs.append((folder, ('verify_all.py', mode)))
        else:
            print(f'Skipping Paper {paper.upper()}: {delegated[paper]}/verify_all.py is not in '
                  'this copy of the repository.', flush=True)

if 'a' in papers and not args.full:
    print('Skipping verify_every_n.py (about 8 min) and verify_every_n_sign.py (about 13 min). '
          'Add --full to run them.', flush=True)
if 'b' in papers and not args.full:
    print('Skipping verify_B_tie_repair.py (about 3 min). Add --full to run it.', flush=True)
if args.dry_run:
    print(f'Commands, in order, run in {base} unless a folder is named:')
for folder, run in runs:
    label = ' '.join(run)
    where = '' if folder == base else f' (in {folder.name})'
    if args.dry_run:
        print(f'  python -B {label}{where}')
        continue
    print(f'\nRunning {label}{where}', flush=True)
    result = subprocess.run([sys.executable, '-B', str(folder / run[0]), *run[1:]], cwd=folder)
    if result.returncode:
        sys.exit(result.returncode)
if not runs:
    print('Nothing to run.', flush=True)
elif not args.dry_run:
    print(f'\nAll {len(runs)} runs finished with exit code 0. Read the output of the scripts '
          'that report their checks there (see the docstring of verify_all.py).', flush=True)
