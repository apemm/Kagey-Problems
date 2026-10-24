"""Build tracked paper PDFs without editing manuscript sources or running proofs.

Run from the repository root. The three commands are plan, build, and publish.
Only publish writes Git history; it is intended for the GitHub Actions checkout.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

CONFIG = Path('.github/papers.json')
STATE = Path('.github/latex-build-state.json')
WORK = Path('.pdf-build')
GLOBAL_INPUTS = [str(CONFIG), 'scripts/paper_pdfs.py', '.github/workflows/paper-pdfs.yml']
EXTENSIONS = {'.tex', '.sec', '.bib', '.bst', '.cls', '.sty', '.clo', '.def',
              '.bbx', '.cbx', '.lbx', '.pdf', '.png', '.jpg', '.jpeg', '.eps',
              '.svg', '.csv', '.dat', '.txt', '.tikz', '.pgf'}
ARCHIVES = {'archive', 'removed', 'removed_proofs', '.lake', '__pycache__'}
BAD_REFERENCES = re.compile(
    r'(?:LaTeX Warning: (?:There were undefined references|There were multiply-defined labels|'
    r'(?:Reference|Citation) .+ undefined)|'
    r'Package (?:xr|xr-hyper) Warning: No file)', re.MULTILINE)


def git(*args):
    return subprocess.check_output(['git', *args]).decode('utf-8').strip()


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')


def summary(message):
    print(message, flush=True)
    if os.environ.get('GITHUB_STEP_SUMMARY'):
        with open(os.environ['GITHUB_STEP_SUMMARY'], 'a', encoding='utf-8') as out:
            out.write(message + '\n\n')


def below(path, directory):
    return path == directory or path.startswith(directory.rstrip('/') + '/')


def source_files(group, tracked, outputs):
    prefixes = [group['directory'], *group.get('extra_inputs', [])]
    excluded = [group['directory'] + '/' + item for item in group.get('exclude', [])]
    return sorted(p for p in tracked if p not in outputs
                  and Path(p).suffix.lower() in EXTENSIONS
                  and not ARCHIVES.intersection(Path(p).parts)
                  and any(below(p, prefix) for prefix in prefixes)
                  and not any(below(p, prefix) for prefix in excluded))


def dependency_order(config, selected):
    order, visiting = [], set()

    def visit(name):
        if name in visiting:
            raise ValueError('Circular paper dependency: ' + name)
        if name not in order:
            visiting.add(name)
            for dependency in config[name].get('depends_on', []):
                visit(dependency)
            visiting.remove(name)
            order.append(name)

    for name in selected:
        visit(name)
    return order


def fingerprints(config, tracked, read_bytes):
    outputs = {str(Path(g['directory'], root).with_suffix('.pdf')).replace('\\', '/')
               for g in config.values() for root in g['roots']}
    result, inputs = {}, {}
    for name in dependency_order(config, config):
        group = config[name]
        inputs[name] = sorted(set(source_files(group, tracked, outputs) + GLOBAL_INPUTS))
        digest = hashlib.sha256()
        for path in inputs[name]:
            digest.update(path.encode() + b'\0')
            digest.update(hashlib.sha256(read_bytes(path)).digest())
        for dependency in group.get('depends_on', []):
            digest.update(result[dependency].encode())
        result[name] = digest.hexdigest()
    return result, inputs


def plan(force=False):
    config = json.loads(CONFIG.read_text(encoding='utf-8'))
    tracked = git('ls-files', '-z').split('\0')
    for group in config.values():
        for root in group['roots']:
            path = (Path(group['directory']) / root).as_posix()
            if path not in tracked:
                raise ValueError('Main document is not tracked: ' + path)
    hashes, inputs = fingerprints(config, tracked, lambda p: Path(p).read_bytes())
    previous = json.loads(STATE.read_text()) if STATE.exists() else {}
    selected = [name for name in config if force or previous.get(name) != hashes[name]]
    order = dependency_order(config, selected)
    epochs = {name: git('log', '-1', '--format=%ct', '--', *inputs[name]) for name in order}
    data = {'source_sha': git('rev-parse', 'HEAD'), 'groups': config,
            'order': order, 'hashes': hashes, 'epochs': epochs}
    write_json(WORK / 'plan.json', data)
    if os.environ.get('GITHUB_OUTPUT'):
        with open(os.environ['GITHUB_OUTPUT'], 'a') as out:
            out.write('needed=' + str(bool(order)).lower() + '\n')
    summary('Papers to compile: ' + ', '.join(order) if order else 'All paper PDFs are up to date.')


def auxiliary_signature(directory, roots):
    return {root + suffix: (directory / Path(root).with_suffix(suffix)).read_bytes()
            for root in roots for suffix in ('.aux', '.out', '.toc')
            if (directory / Path(root).with_suffix(suffix)).exists()}


def compile_group(name, group, epoch):
    directory = Path(group['directory'])
    roots = group['roots']
    environment = {**os.environ, 'SOURCE_DATE_EPOCH': str(epoch), 'FORCE_SOURCE_DATE': '1'}
    previous = None
    for turn in range(1, 7):
        for root in roots:
            transcript = WORK / 'logs' / name / (Path(root).stem + f'-pass{turn}.txt')
            transcript.parent.mkdir(parents=True, exist_ok=True)
            with transcript.open('w', encoding='utf-8') as out:
                result = subprocess.run(
                    ['pdflatex', '-no-shell-escape', '-halt-on-error', '-file-line-error',
                     '-interaction=nonstopmode', '-recorder', root],
                    cwd=directory, env=environment, stdout=out, stderr=subprocess.STDOUT,
                    timeout=180)
            if result.returncode:
                print(transcript.read_text(errors='replace')[-8000:], flush=True)
                raise RuntimeError(f'{name}/{root} failed on pass {turn}; see {transcript}')
        current = auxiliary_signature(directory, roots)
        if turn >= 3 and current == previous:
            break
        previous = current
    else:
        raise RuntimeError(f'{name}: references did not stabilize after six passes')
    pdfs = []
    for root in roots:
        log_path = directory / Path(root).with_suffix('.log')
        log = log_path.read_text(errors='replace')
        shutil.copyfile(log_path, WORK / 'logs' / name / log_path.name)
        if BAD_REFERENCES.search(log) or 'Rerun to get cross-references right' in log:
            raise RuntimeError(f'{name}/{root}: unresolved or duplicate references; see {log_path}')
        pdf = directory / Path(root).with_suffix('.pdf')
        if not pdf.is_file() or not pdf.read_bytes().startswith(b'%PDF-'):
            raise RuntimeError('Missing or invalid PDF: ' + str(pdf))
        pdfs.append(pdf.as_posix())
        summary(f'Built {pdf.as_posix()} ({turn} passes).')
    return pdfs


def build():
    data = json.loads((WORK / 'plan.json').read_text())
    outputs, failures = [], []
    for name in data['order']:
        try:
            outputs += compile_group(name, data['groups'][name], data['epochs'][name])
        except (RuntimeError, subprocess.TimeoutExpired) as error:
            summary('Build failed: ' + str(error))
            failures.append(name)
    # Do not update the saved state or publish any PDFs from an incomplete build.
    for path in outputs:
        destination = WORK / 'pdfs' / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, destination)
    if failures:
        raise RuntimeError('No PDFs will be committed. Failed groups: ' + ', '.join(failures))
    previous = json.loads(STATE.read_text()) if STATE.exists() else {}
    for name in data['order']:
        previous[name] = data['hashes'][name]
    write_json(STATE, previous)
    write_json(WORK / 'outputs.json', outputs)


def publish():
    if os.environ.get('GITHUB_ACTIONS') != 'true':
        raise RuntimeError('publish is restricted to GitHub Actions')
    data = json.loads((WORK / 'plan.json').read_text())
    branch = os.environ['PDF_BRANCH']
    if git('rev-parse', 'HEAD') != data['source_sha']:
        raise RuntimeError('Checkout changed during compilation')
    # Never attach PDFs built from an older source to a newer source revision.
    git('fetch', 'origin', 'refs/heads/' + branch)
    if git('rev-parse', 'FETCH_HEAD') != data['source_sha']:
        summary('Newer edits arrived during compilation. The queued run will rebuild them; no push made.')
        return
    if git('diff', '--cached', '--name-only'):
        raise RuntimeError('Unexpected staged changes before publishing')
    outputs = json.loads((WORK / 'outputs.json').read_text())
    git('add', '--', *outputs, str(STATE))
    if not git('diff', '--cached', '--name-only'):
        summary('The rebuilt PDFs are unchanged; no commit needed.')
        return
    git('config', 'user.name', 'github-actions[bot]')
    git('config', 'user.email', '41898282+github-actions[bot]@users.noreply.github.com')
    git('commit', '-m', 'Rebuild paper PDFs')
    # A normal push rejects concurrent edits; never force-push or rebase stale PDFs.
    git('push', 'origin', 'HEAD:refs/heads/' + branch)
    summary('Updated PDFs committed to ' + branch + '.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['plan', 'build', 'publish'])
    parser.add_argument('--all', action='store_true', help='rebuild all groups')
    args = parser.parse_args()
    try:
        if args.command == 'plan':
            plan(args.all or os.environ.get('REBUILD_ALL') == 'true')
        elif args.command == 'build':
            build()
        else:
            publish()
    except (RuntimeError, ValueError, subprocess.CalledProcessError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
