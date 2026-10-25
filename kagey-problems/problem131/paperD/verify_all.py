"""Run the 5 check scripts of Paper D with the current interpreter.

verify_elephant_crossing.py checks Section 2, Table 1 and Appendix A, and
verify_elephant_shape.py checks Section 3 and Appendices B and C.
verify_elephant_odd.py checks Proposition 3.21 (odd N) and Section S3 of the
arXiv version. certify_elephant.py certifies the computations behind
Theorem 2.6(b), Proposition 3.7 and Lemma 3.10. verify_elephant_modes.py checks
the constants of Theorem 4.3 and the numbers of Remark 4.4 (Section 4.2), and
writes data/verify_modes_output.txt. certify_center.py and certify_convex.py
take much longer, so this runner does not run them.

The default is the quick run, which takes a few minutes. Add --full for the
heavy cells of the first 2 scripts (the second method at the largest n, the
case n = 25600 and the slow bridge sums at n = 12800).
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
           'verify_elephant_odd.py',        # Proposition 3.21 (odd N) and Section S3
           'certify_elephant.py',           # Theorem 2.6(b), Proposition 3.7, Lemma 3.10 (needs python-flint)
           'verify_elephant_modes.py')      # Theorem 4.3 and Remark 4.4 (needs python-flint)
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
