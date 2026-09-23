"""Run every Problem 131 check using the current Python interpreter."""
from pathlib import Path
import subprocess
import sys

base = Path(__file__).resolve().parent
scripts = ('verify.py', 'check_bessel.py', 'verify_geometry.py', 'verify_adjacent.py',
           'verify_allbin.py', 'verify_periodic_window.py', 'verify_simplex_threshold.py',
           'verify_frontier_boundary.py', 'verify_frontier_modes.py',
           'verify_vertex_completion.py')
for name in scripts:
    print(f'\nRunning {name}', flush=True)
    result = subprocess.run([sys.executable, '-B', str(base / name)], cwd=base)
    if result.returncode:
        sys.exit(result.returncode)
print(f'\nAll {len(scripts)} verification scripts passed.', flush=True)
