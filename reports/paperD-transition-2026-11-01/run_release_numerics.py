"""Run the numerical suite from an isolated export of a specified source commit."""
from pathlib import Path
import argparse
import hashlib
import importlib.metadata
import json
import platform
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--commit', required=True)
args = parser.parse_args()
commit = subprocess.check_output(
    ['git', 'rev-parse', '--verify', '--end-of-options', args.commit + '^{commit}'],
    cwd=ROOT, text=True).strip()
if len(commit) != 40 or any(c not in '0123456789abcdef' for c in commit):
    raise RuntimeError('Expected a resolved commit SHA')
build = ROOT / '.pdf-build'
build.mkdir(exist_ok=True)
export = Path(tempfile.mkdtemp(prefix=f'paperD-release-{commit[:12]}-', dir=build)).resolve()
archive = export / 'source.zip'
subprocess.run(['git', 'archive', '--format=zip', f'--output={archive}', commit,
                'kagey-problems/problem131/verify_all.py',
                'kagey-problems/problem131/paperD'], cwd=ROOT, check=True)
with zipfile.ZipFile(archive) as package:
    for member in package.infolist():
        target = (export / member.filename).resolve()
        if not target.is_relative_to(export):
            raise RuntimeError(f'Unsafe archive entry: {member.filename}')
    package.extractall(export)

log = HERE / 'release-numerical-verification.txt'
command = [sys.executable, '-B',
           str(export / 'kagey-problems/problem131/verify_all.py'), '--paper', 'd']
with log.open('w', encoding='utf-8') as stream:
    stream.write(f'Source commit: {commit}\nIsolated export: {export}\n')
    stream.flush()
    result = subprocess.run(command, cwd=export, stdout=stream, stderr=subprocess.STDOUT,
                            timeout=3600)
record = {
    'source_commit': commit,
    'exit_code': result.returncode,
    'all_checks_passed': result.returncode == 0,
    'export_directory': str(export),
    'command': command,
    'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest(),
    'python': platform.python_version(),
    'dependencies': {name: importlib.metadata.version(name)
                     for name in ('numpy', 'scipy', 'mpmath', 'python-flint')},
    'scope': 'Seven-script quick suite; checks archived threshold records and three fresh probes, then freshly runs the complete transition-derivative certificate at 1600 bits with 1100 moments. It does not rerun all nine original full threshold jobs.',
}
(HERE / 'release-numerical-verification.json').write_text(
    json.dumps(record, indent=2) + '\n', encoding='utf-8')
print(json.dumps(record, indent=2), flush=True)
raise SystemExit(result.returncode)
