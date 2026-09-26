"""Run the checks for Paper C with the current interpreter.

The default (--quick) reproduces the numbers of the paper that take a few
minutes in all. Add --full for the heavy cells as well: the directed 3-cycle at
N = 10^8, the whole 4-cycle in the continuum, C_5 at N = 72, the path P_4 at
N = 150 and 300, the census of graphs on 6 states, the planar crossings from
N = 1280 to 10240, the sticky switches at N = 480, the telegraph comparison at
N = 16000, and the cells at N = 160 of the first-order section.
Needs numpy, scipy, sympy and mpmath.
"""
from pathlib import Path
import argparse
import subprocess
import sys
import time

base = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
group = parser.add_mutually_exclusive_group()
group.add_argument('--quick', action='store_true', help='the default')
group.add_argument('--full', action='store_true', help='also run the heavy cells')
args = parser.parse_args()
# one script per topic, matching the ledgers ledger_C1.md to ledger_C5.md
scripts = ('verify_first_order.py',      # C1: exact law, the rate on a face, first-order selection
           'verify_examples.py',         # C2: complete graphs, cycles, paths, 2 triangles, the paw and the house
           'verify_planar.py',           # C3: the planar persistent walk
           'verify_sticky_fisher.py',    # C4: sticky priors and the endpoint Fisher information
           'verify_second_order.py')     # C5: the local law, the constants and the crossings
t0 = time.time()
for name in scripts:
    print(f'\nRunning {name}' + (' --full' if args.full else ''), flush=True)
    cmd = [sys.executable, '-B', str(base / name)] + (['--full'] if args.full else [])
    result = subprocess.run(cmd, cwd=base)
    if result.returncode:
        sys.exit(result.returncode)
print(f'\nAll {len(scripts)} verification scripts passed ({time.time() - t0:.0f} s).', flush=True)
