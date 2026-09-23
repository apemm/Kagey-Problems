"""Run the checks for Paper A, Paper B, or both using the current interpreter."""
from pathlib import Path
import argparse
import subprocess
import sys

base = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--paper', choices=('a', 'b', 'all'), default='all')
args = parser.parse_args()
paper_a = ('verify.py', 'check_bessel.py', 'verify_adjacent.py',
           'verify_allbin.py', 'verify_periodic_window.py')
paper_b = ('verify_geometry.py', 'verify_simplex_threshold.py',
           'verify_frontier_boundary.py', 'verify_frontier_modes.py',
           'verify_vertex_completion.py')
scripts = paper_a if args.paper == 'a' else paper_b if args.paper == 'b' else paper_a + paper_b
for name in scripts:
    print(f'\nRunning {name}', flush=True)
    result = subprocess.run([sys.executable, '-B', str(base / name)], cwd=base)
    if result.returncode:
        sys.exit(result.returncode)
print(f'\nAll {len(scripts)} verification scripts passed.', flush=True)
