"""Run the checks for Paper F (heavy-tailed runs and aging walks) with the current interpreter.

The default is the quick run, which takes a few minutes. Add --full for the heavy cells
(the slow sums and the grid search for the crossover size). Needs numpy, scipy and mpmath.
"""
from pathlib import Path
import argparse
import subprocess
import sys
import time

base = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__.split('\n')[0])
mode = parser.add_mutually_exclusive_group()
mode.add_argument('--quick', action='store_true', help='quick run (the default)')
mode.add_argument('--full', action='store_true', help='also run the heavy cells')
args = parser.parse_args()
scripts = ('verify_heavy_runs.py',          # Section 2, the tables, Appendix A
           'verify_aging.py',               # Section 3, Appendix B
           'verify_aging_urn.py')           # the chain that redraws or repeats, in exact arithmetic
extra = ['--full'] if args.full else []
start = time.time()
failed = []
for name in scripts:
    print(f'\n=== Running {name} {" ".join(extra)}'.rstrip(), flush=True)
    result = subprocess.run([sys.executable, '-B', str(base / name)] + extra, cwd=base)
    if result.returncode:
        failed.append(name)
minutes = (time.time() - start) / 60
if failed:
    print(f'\n{len(failed)} of {len(scripts)} scripts reported failures: {", ".join(failed)} '
          f'({minutes:.1f} min).', flush=True)
    sys.exit(1)
print(f'\nAll {len(scripts)} verification scripts passed ({minutes:.1f} min).', flush=True)
