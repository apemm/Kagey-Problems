"""Run the checks for Paper D, one script per section, with the current interpreter.

The default is the quick run, which takes a few minutes. Add --full for the
heavy cells (second methods on the largest sizes, the slow bridge sums, and the
grid search for n*(1.60)). The full run takes about 45 minutes.
Needs numpy, scipy, mpmath and python-flint.
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
scripts = ('verify_elephant_crossing.py',   # Section 2, Table 1, Appendix A
           'verify_elephant_shape.py',      # Section 3, Appendices B and C
           'verify_heavy_runs.py',          # Section 4, Tables 2 and 3, Appendix D
           'verify_aging.py',               # Section 5, Appendix E
           'verify_aging_urn.py',           # Proposition 5.4 (fresh or repeat)
           'certify_elephant.py')           # Lemma 3.7, Proposition 3.8, Lemma 3.11 (needs python-flint)
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
