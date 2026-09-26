"""Run the checks for Papers A to D of Problem 131 with the current interpreter.

Each paper has its own runner, paperA/verify_all.py to paperD/verify_all.py, and runs its scripts
in its own folder. This script calls those runners in turn with --quick, or with --full when --full
is given. The quick runs take about 2 minutes each for Papers A and B and a few minutes each for
Papers C and D. With --full, Paper A takes about 21 minutes more, Paper B about 3 minutes more,
Paper C up to about half an hour and Paper D about 45 minutes.

If a paper folder is missing, this script says so in one line and goes on. A runner that stops
with a nonzero exit code stops this script too. With --dry-run the commands are printed and
nothing is run.

The scripts of Papers A and B use only the standard library. Those of Papers C and D need numpy,
scipy and mpmath, and Paper C also needs sympy. Some scripts of Papers A and B report their checks
in their output rather than through the exit code, and the docstrings of paperA/verify_all.py and
paperB/verify_all.py say which ones.
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
                    help='also run the long scripts of Papers A and B (about 21 and 3 minutes '
                         'more) and the heavy cells of Papers C and D')
parser.add_argument('--dry-run', action='store_true',
                    help='print the commands in order and run nothing')
args = parser.parse_args()

mode = '--full' if args.full else '--quick'
papers = 'abcd' if args.paper == 'all' else args.paper
runs = []          # (paper, folder)
for paper in papers:
    folder = base / f'paper{paper.upper()}'
    if (folder / 'verify_all.py').is_file():
        runs.append((paper.upper(), folder))
    else:
        print(f'Skipping Paper {paper.upper()}: {folder.name}/verify_all.py is not in this copy '
              'of the repository.', flush=True)

if args.dry_run and runs:
    print(f'Commands, in order, each run in its paper folder under {base}:')
for paper, folder in runs:
    if args.dry_run:
        print(f'  python -B verify_all.py {mode} (in {folder.name})')
        continue
    print(f'\n=== Paper {paper}: python -B verify_all.py {mode} (in {folder.name})', flush=True)
    result = subprocess.run([sys.executable, '-B', str(folder / 'verify_all.py'), mode],
                            cwd=folder)
    if result.returncode:
        print(f'\nPaper {paper} stopped with exit code {result.returncode}.', flush=True)
        sys.exit(result.returncode)
if not runs:
    print('Nothing to run.', flush=True)
elif not args.dry_run:
    names = [paper for paper, _ in runs]
    if len(names) == 1:
        done = f'The runner of Paper {names[0]}'
    else:
        done = f'The runners of Papers {", ".join(names[:-1])} and {names[-1]}'
    print(f'\n{done} finished with exit code 0. Read the output of the scripts that report their '
          'checks there (see paperA/verify_all.py and paperB/verify_all.py).', flush=True)
