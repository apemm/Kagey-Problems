"""Run the checks for Papers A to F and the note S4 of Problem 131 with the current interpreter.

Each paper has its own runner, paperA/verify_all.py to paperF/verify_all.py, and runs its scripts
in its own folder. With --paper c this script runs the runner of Paper C1 in paperC, and with
--paper c2 that of Paper C2 in paperC2. It calls the runners in turn with --quick, or with --full
when --full is given. The runner of Paper C2 takes neither flag, so it is called with none. The
note S4 (S4_aging_note) has no runner of its own, so this script runs its 2 check scripts,
verify_aging.py (with --full when --full is given) and verify_aging_urn.py, in that folder.
The quick runs take about 2 minutes each for Papers A and B, about nine and a half minutes for
Paper C1 (8 scripts in 567 s on October 24, 2026), under 3 minutes for Paper C2 (5 scripts in
157 s that day), a few minutes for Paper D, under a minute for Paper F and under a minute for the
note. With --full, Paper A takes about 21 minutes more, Paper B about 3 minutes more, Paper C1 a
few minutes more (the largest cases of four scripts, about 4 minutes of them for S = 64 in
verify_layer_general.py), Paper E up to about half an hour, Paper D up to about 45 minutes and
Paper F about 2 minutes in all. Paper C2 runs the same with or without --full.
(Papers E and F were split off Papers C and D in October 2026, and Paper B was merged into Paper C.
On October 24, 2026 Paper C was split into Paper C1, which keeps the folder paperC and the results
of Paper B, and Paper C2 in paperC2. With --paper b this script still runs the checks of Paper B,
which also cover the statements of Paper C1 that came from Paper B. On October 24, 2026 the first
draft of Paper F was archived in archive/paperF_golden_aging, with its own runner, and Paper F was
started again in paperF. The checks of the aging walk moved with the note, so --paper s4 runs
them.)

If a paper folder or its runner is missing, this script says so in one line and goes on. A runner
that stops with a nonzero exit code stops this script too. With --dry-run the commands are printed
and nothing is run.

The scripts of Papers A and B use only the standard library. Those of Papers C1, C2, D and F and
of the note need numpy, scipy and mpmath. Paper E needs numpy and scipy. Papers C1 and C2 also
need sympy, and Papers D and F also need python-flint. Some scripts of Papers A and B report their checks
in their output rather than through the exit code, and the docstrings of paperA/verify_all.py and
archive/paperB/verify_all.py say which ones.
"""
from pathlib import Path
import argparse
import subprocess
import sys

base = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
parser.add_argument('--paper', choices=('a', 'b', 'c', 'c2', 'd', 'e', 'f', 's4', 'all'),
                    default='all')
parser.add_argument('--full', action='store_true',
                    help='also run the long scripts of Papers A and B (about 21 and 3 minutes '
                         'more) and the heavy cells of Papers C to F and of the note S4')
parser.add_argument('--dry-run', action='store_true',
                    help='print the commands in order and run nothing')
args = parser.parse_args()

mode = '--full' if args.full else '--quick'
papers = ['a', 'b', 'c', 'c2', 'd', 'e', 'f', 's4'] if args.paper == 'all' else [args.paper]
runs = []          # (name, folder, [(script, arguments)])
for paper in papers:
    if paper == 's4':
        name, folder = 'note S4', base / 'S4_aging_note'
        scripts = [('verify_aging.py', ['--full'] if args.full else []),
                   ('verify_aging_urn.py', [])]
    elif paper == 'c':
        name, folder = 'Paper C1', base / 'paperC'
        scripts = [('verify_all.py', [mode])]
    elif paper == 'c2':
        name, folder = 'Paper C2', base / 'paperC2'
        scripts = [('verify_all.py', [])]
    else:
        name = f'Paper {paper.upper()}'
        folder = base / 'archive/paperB' if paper == 'b' else base / f'paper{paper.upper()}'
        scripts = [('verify_all.py', [mode])]
    missing = [script for script, _ in scripts if not (folder / script).is_file()]
    if missing:
        print(f'Skipping {name}: {folder.relative_to(base)}/{missing[0]} is not in this copy '
              'of the repository.', flush=True)
    else:
        runs.append((name, folder, scripts))

if args.dry_run and runs:
    print(f'Commands, in order, each run in its folder under {base}:')
for name, folder, scripts in runs:
    for script, extra in scripts:
        command = ' '.join(['python -B', script] + extra)
        if args.dry_run:
            print(f'  {command} (in {folder.relative_to(base)})')
            continue
        print(f'\n=== {name}: {command} (in {folder.relative_to(base)})', flush=True)
        result = subprocess.run([sys.executable, '-B', str(folder / script)] + extra, cwd=folder)
        if result.returncode:
            print(f'\n{name} stopped with exit code {result.returncode} ({script}).', flush=True)
            sys.exit(result.returncode)
if not runs:
    print('Nothing to run.', flush=True)
elif not args.dry_run:
    names = [name for name, _, _ in runs]
    if len(names) == 1:
        done = f'The checks of {names[0]}'
    else:
        done = f'The checks of {", ".join(names[:-1])} and {names[-1]}'
    print(f'\n{done} finished with exit code 0. Read the output of the scripts that report their '
          'checks there (see paperA/verify_all.py and archive/paperB/verify_all.py).', flush=True)
