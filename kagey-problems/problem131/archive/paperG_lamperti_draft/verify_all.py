"""Run the check scripts of Paper G with the current interpreter.

verify_identities.py checks the exact identities of Section 2 against a sum over all sign strings.
verify_shape.py checks the threshold of Theorem thm:shape, the transform of Proposition prop:lambda
and the double integral of Theorem thm:local at a = 1/2. verify_local.py computes the exact law at
N = 1000, 2000, 4000 and checks the ratios, end layers and sign changes quoted in Section sec:verify.
verify_initial.py checks the numbers on the initial run (Theorem thm:initial, Remark rem:aging).

The whole run takes about a minute. Needs numpy, scipy and mpmath. Each script writes its output with
its sha256 and the date to data/, and this runner writes its summary to data/verify_all_output.txt.
"""
from datetime import date
from pathlib import Path
import hashlib
import platform
import subprocess
import sys
import time

base = Path(__file__).resolve().parent
scripts = ['verify_identities.py',   # Section 2, exact identities, N <= 12
           'verify_shape.py',        # thm:shape, prop:lambda, thm:local(a)
           'verify_local.py',        # sec:verify, exact law at N = 1000, 2000, 4000
           'verify_initial.py']      # thm:initial, rem:aging
start = time.time()
failed = []
times = []
for name in scripts:
    print(f'\n=== Running {name}', flush=True)
    t0 = time.time()
    result = subprocess.run([sys.executable, '-I', '-B', str(base / name)], cwd=base)
    times.append((name, time.time() - t0, result.returncode))
    if result.returncode:
        failed.append(name)
summary = []
for name, dt, rc in times:
    summary.append(f'{"PASS" if rc == 0 else "FAIL"}  {name}  ({dt:.1f} s)  '
                   f'sha256 {hashlib.sha256((base / name).read_bytes()).hexdigest()}')
minutes = (time.time() - start) / 60
if failed:
    summary.append(f'{len(failed)} of {len(scripts)} scripts reported failures: {", ".join(failed)} '
                   f'({minutes:.1f} min).')
else:
    summary.append(f'All {len(scripts)} scripts passed ({minutes:.1f} min).')
print('\n=== Summary', flush=True)
print('\n'.join(summary), flush=True)
header = ['# script: verify_all.py',
          f'# sha256: {hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}',
          f'# uses lamperti_law.py sha256: {hashlib.sha256((base / "lamperti_law.py").read_bytes()).hexdigest()}',
          f'# date: {date.today().isoformat()}',
          f'# python {platform.python_version()}',
          '# the output of each script is in data/verify_*_output.txt', '']
out = base / 'data' / 'verify_all_output.txt'
out.write_text('\n'.join(header + summary) + '\n', encoding='utf-8', newline='\n')
sys.exit(1 if failed else 0)
