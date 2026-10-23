"""Run the checks for Paper C with the current interpreter.

The default (--quick) reproduces the numbers of the paper that take a few
minutes in all. Add --full for the heavy cells as well: the directed 3-cycle at
N = 10^8, the whole 4-cycle in the continuum, C_5 at N = 72, the path P_4 at
N = 150 and 300, the census of graphs on 6 states, the sticky switches at
N = 480, the telegraph comparison at N = 16000, and the cells at N = 160 of the
first-order section. The planar cells are now in ../paperE.
Needs numpy, scipy, sympy and mpmath.

Since October 2026 this paper incorporates Paper B (../paperB). The checks of the statements that
came from Paper B are the scripts of ../paperB, run by ../paperB/verify_all.py (or
`python -B verify_all.py --paper b` in the folder problem131). The sticky-prior checks in
verify_sticky_fisher.py belong to the note ../S3_sticky_note, and its Fisher checks to the note
../S1_endpoint_information_note.
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
           'verify_sticky_fisher.py',    # C4: sticky priors (now the note S3) and the endpoint information note S1
           'verify_second_order.py',     # C5: the local law, the constants and the crossings
           'verify_forest.py',           # Proposition 4.9 and Lemma A.3: the tree formula (about five minutes)
           'verify_rate_flows.py',       # Remark 4.12: the rate through flows
           'verify_weak_field.py')       # Proposition 4.16: a weak field (about a minute)
t0 = time.time()
for name in scripts:
    print(f'\nRunning {name}' + (' --full' if args.full else ''), flush=True)
    cmd = [sys.executable, '-B', str(base / name)] + (['--full'] if args.full else [])
    result = subprocess.run(cmd, cwd=base)
    if result.returncode:
        sys.exit(result.returncode)
print(f'\nAll {len(scripts)} verification scripts passed ({time.time() - t0:.0f} s).', flush=True)
