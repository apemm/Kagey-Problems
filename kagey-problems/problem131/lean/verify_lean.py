"""Compile all Problem 131 Lean files and check every printed axiom set."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
from datetime import datetime, timezone

base = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--lean', default='lean')
args = parser.parse_args()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
version = subprocess.check_output([args.lean, '--version'], text=True).strip()
manifest = {'checked_at_utc': datetime.now(timezone.utc).isoformat(),
            'lean_version': version, 'full_analytic_theorems_formalized': False, 'modules': []}
logs = []
for module in ['FiniteBessel', 'RunAlgebra', 'EdgeExpansion']:
    source_path = base / (module+'.lean')
    source = source_path.read_text(encoding='utf-8-sig')
    names = re.findall(r'^theorem\s+(\w+)', source, flags=re.M)
    declared = {'Kagey131.'+name for name in names}
    process = subprocess.run([args.lean, str(source_path)], cwd=base,
                             capture_output=True, text=True, encoding='utf-8', timeout=180)
    output = process.stdout+process.stderr
    logs.append(f'=== {module}: exit {process.returncode} ===\n{output}\n')
    (base/'build-log.txt').write_text(''.join(logs), encoding='utf-8')
    if process.returncode or 'warning:' in output:
        raise RuntimeError(output)
    deps = {}
    for name, items in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, flags=re.S):
        deps[name] = sorted(x.strip() for x in items.split(',') if x.strip())
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        deps[name] = []
    if set(deps) != declared:
        raise RuntimeError(f'{module}: theorem audit mismatch: {set(deps)^declared}')
    if any(set(v)-allowed for v in deps.values()):
        raise RuntimeError(f'{module}: unexpected axioms {deps}')
    manifest['modules'].append({'module': module, 'theorem_count': len(names),
                                'sha256': hashlib.sha256(source_path.read_bytes()).hexdigest(),
                                'exit_code': 0, 'axioms': deps})
    print(f'{module}: {len(names)} theorems; compiled; all axioms checked.', flush=True)
manifest['total_theorem_declarations'] = sum(m['theorem_count'] for m in manifest['modules'])
manifest['all_checks_passed'] = True
(base/'verification-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print(f'Total: {manifest["total_theorem_declarations"]} finite-arithmetic theorem declarations.')
