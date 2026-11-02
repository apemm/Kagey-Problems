"""Rebuild the committed Paper D library and check it against the full audit."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--commit', required=True)
parser.add_argument('--workspace', required=True, type=Path)
parser.add_argument('--toolchain', required=True, type=Path)
args = parser.parse_args()
commit = subprocess.check_output(
    ['git', 'rev-parse', '--verify', '--end-of-options', args.commit + '^{commit}'],
    cwd=ROOT, text=True).strip()
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
if head != commit:
    raise RuntimeError('The source commit must be the current checkout')
subprocess.run(['git', 'diff', '--exit-code', commit, '--',
                'kagey-problems/problem131/paperD',
                'kagey-problems/problem131/lean'], cwd=ROOT, check=True)
subprocess.run([sys.executable, '-B', str(HERE / 'check_final_state.py')],
               cwd=ROOT, check=True)
env = dict(os.environ)
env['PATH'] = str(args.toolchain) + os.pathsep + env.get('PATH', '')
command = [str(args.toolchain / 'lake.exe'), 'build', 'PaperD']
log = HERE / 'release-lean-build.txt'
with log.open('w', encoding='utf-8') as stream:
    stream.write(f'Source commit: {commit}\n')
    stream.flush()
    result = subprocess.run(command, cwd=args.workspace, env=env,
                            stdout=stream, stderr=subprocess.STDOUT, timeout=3600)
text = log.read_text(encoding='utf-8')
if result.returncode or "declaration uses 'sorry'" in text:
    raise RuntimeError('Committed-source Lean build failed; inspect its log')
manifest = json.loads((HERE / 'verification-manifest.json').read_text())
entry = manifest['libraries']['PaperD']
record = {
    'source_commit': commit,
    'all_checks_passed': True,
    'build_exit_code': result.returncode,
    'build_log_sha256': hashlib.sha256(log.read_bytes()).hexdigest(),
    'full_axiom_audit_sha256': hashlib.sha256(
        (HERE / 'verification-manifest.json').read_bytes()).hexdigest(),
    'audited_module_count': entry['module_count'],
    'audited_declaration_count': entry['declaration_count'],
    'audited_sources_unchanged': True,
    'command': command,
    'workspace': str(args.workspace),
    'scope': 'Rebuild at the source commit. The earlier full import/axiom audit covers identical source bytes; check_final_state.py rechecks each hash.',
}
(HERE / 'release-lean-verification.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
