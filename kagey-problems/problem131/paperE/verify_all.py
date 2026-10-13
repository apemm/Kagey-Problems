"""Run the checks for Paper E (the planar persistent walk) with the current interpreter.

The default (--quick) takes a few minutes. Add --full for the planar crossings from
N = 1280 to 10240. Needs numpy and scipy. verify_planar.py imports Paper A's polynomial S_N
from ../paperC/verify_sticky_fisher.py, so the folder paperC must be present.
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
scripts = ('verify_planar.py',           # the planar persistent walk (ledger_C3.md)
           'verify_planar_product.py')   # the product curve and turns only
t0 = time.time()
for name in scripts:
    print(f'\nRunning {name}' + (' --full' if args.full else ''), flush=True)
    cmd = [sys.executable, '-B', str(base / name)] + (['--full'] if args.full else [])
    result = subprocess.run(cmd, cwd=base)
    if result.returncode:
        sys.exit(result.returncode)
print(f'\nAll {len(scripts)} verification scripts passed ({time.time() - t0:.0f} s).', flush=True)
