"""Check proof-source hashes, the released manuscript and release references."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
LEAN = ROOT / 'kagey-problems/problem131/lean'
PAPER = ROOT / 'kagey-problems/problem131/paperD'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


manifest = json.loads((HERE / 'verification-manifest.json').read_text())
require(manifest['all_checks_passed'] is True, 'The full Lean audit did not pass')
entry = manifest['libraries']['PaperD']
manuscript_commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
audited_files = [m['file'] for m in entry['modules']]
audited_inventory = set(audited_files)
require(len(audited_files) == len(audited_inventory), 'The Lean manifest repeats a module path')
require(entry['module_count'] == len(audited_files), 'The Lean manifest module count is inconsistent')
current_inventory = {p.relative_to(LEAN).as_posix()
                     for p in (LEAN / 'PaperD').rglob('*.lean')}
if (LEAN / 'PaperD.lean').is_file():
    current_inventory.add('PaperD.lean')
require(current_inventory == audited_inventory,
        'The current Lean inventory differs from the audit: '
        f'added={sorted(current_inventory - audited_inventory)}, '
        f'missing={sorted(audited_inventory - current_inventory)}')

lean_prefix = LEAN.relative_to(ROOT).as_posix() + '/'
committed_paths = subprocess.check_output(
    ['git', 'ls-tree', '-r', '--name-only', manuscript_commit, '--',
     lean_prefix + 'PaperD', lean_prefix + 'PaperD.lean'],
    cwd=ROOT, text=True).splitlines()
committed_inventory = {p[len(lean_prefix):] for p in committed_paths if p.endswith('.lean')}
require(committed_inventory == audited_inventory,
        'The committed Lean inventory differs from the audit: '
        f'unaudited={sorted(committed_inventory - audited_inventory)}, '
        f'uncommitted={sorted(audited_inventory - committed_inventory)}')

checkout_line_endings = []
for module in entry['modules']:
    name = module['file']
    current_bytes = (LEAN / name).read_bytes()
    require(hashlib.sha256(current_bytes).hexdigest() == module['sha256'],
            f'Lean source changed after the audit: {name}')
    committed_bytes = subprocess.check_output(
        ['git', 'show', f'{manuscript_commit}:{lean_prefix}{name}'], cwd=ROOT)
    # Git checks out older text modules with CRLF on Windows. Permit only that
    # byte conversion, and independently verify Git's own clean-filter result.
    if committed_bytes != current_bytes and committed_bytes == current_bytes.replace(b'\r\n', b'\n'):
        checkout_line_endings.append(name)
        cleaned_blob = subprocess.check_output(
            ['git', 'hash-object', '--path=' + lean_prefix + name, '--stdin'],
            cwd=ROOT, input=current_bytes).decode().strip()
        committed_blob = subprocess.check_output(
            ['git', 'rev-parse', f'{manuscript_commit}:{lean_prefix}{name}'],
            cwd=ROOT, text=True).strip()
        require(cleaned_blob == committed_blob, f'Git source normalization differs: {name}')
    require(committed_bytes == current_bytes or name in checkout_line_endings,
            f'Committed and audited worktree Lean bytes differ: {name}; '
            f'commit_sha256={hashlib.sha256(committed_bytes).hexdigest()}, '
            f'worktree_sha256={hashlib.sha256(current_bytes).hexdigest()}')

tex = (PAPER / 'problem131_memory.tex').read_text(encoding='utf-8')
released_source = subprocess.check_output(
    ['git', 'show', f'{manuscript_commit}:kagey-problems/problem131/paperD/problem131_memory.tex'],
    cwd=ROOT).decode('utf-8').replace('\r\n', '\n')
require(tex == released_source, 'The manuscript differs from the verified release')
manuscript_hash = hashlib.sha256(tex.encode()).hexdigest()

metadata = json.loads((PAPER / 'arxiv_metadata.json').read_text())
tag = 'paperD-arxiv-v3'
for section in ('Data availability.', 'Code availability.'):
    part = tex.split(r'\paragraph{' + section + '}', 1)[1].split(r'\paragraph{', 1)[0]
    refs = re.findall(r'github\.com/apemm/Kagey-Problems/tree/([^/}]+)', part)
    require(refs and set(refs) == {tag}, f'Incorrect release reference in {section}: {refs}')
require(f'tag {tag}' in metadata['comments'], 'Metadata has the wrong release reference')
require(tag in (PAPER / 'README.md').read_text(encoding='utf-8'), 'README lacks the release reference')

baseline = '7e78cbad17b2dc60101363d09275e0ee5067c4d5'
old_intro = subprocess.check_output(
    ['git', 'show', f'{baseline}:kagey-problems/problem131/paperD/sec_intro.tex'],
    cwd=ROOT).decode('utf-8').replace('\r\n', '\n')
new_intro = (PAPER / 'sec_intro.tex').read_text(encoding='utf-8')
quote_pattern = r'\\begin\{quote\}.*?\\medskip'
require(re.search(quote_pattern, old_intro, re.S).group() ==
        re.search(quote_pattern, new_intro, re.S).group(), 'The epigraph changed')
callback = ('As in the riddle, the evidence is left at the door: a walk that ends in the\n'
            'middle usually shows a reversal among its first few steps.')
require(callback in new_intro, 'The epigraph callback changed')
old_main = subprocess.check_output(
    ['git', 'show', f'{baseline}:kagey-problems/problem131/paperD/problem131_memory.tex'],
    cwd=ROOT).decode('utf-8').replace('\r\n', '\n')
ack_pattern = r'\\section\*\{Acknowledgments\}.*?(?=\\clearpage)'
require(re.search(ack_pattern, old_main, re.S).group() ==
        re.search(ack_pattern, tex, re.S).group(), 'The acknowledgments changed')

certificate = json.loads((PAPER / 'data/transition_derivative_certificate.json').read_text())
require(certificate['all_checks_passed'] is True and all(certificate['checks'].values()),
        'The derivative certificate did not pass')
for name, digest in certificate['source_sha256'].items():
    require(hashlib.sha256((PAPER / name).read_bytes()).hexdigest() == digest,
            f'Derivative certificate source changed: {name}')

# The reviewed certificate files have LF endings in Git and in the worktree.
reviewed = 'b3fe9977af42c87aa0b627e736d2d34c7befe696'
certificate_files = ['certify_threshold.py', 'threshold_taylor.py',
                     'threshold_hankel.py', 'threshold_pointwise.py']
certificate_files += [str(p.relative_to(PAPER)).replace('\\', '/')
                      for p in sorted((PAPER / 'data').glob('threshold_*.txt'))]
certificate_files += ['data/certify_threshold_output.txt']
for name in certificate_files:
    archived = subprocess.check_output(
        ['git', 'show', f'{reviewed}:kagey-problems/problem131/paperD/{name}'], cwd=ROOT)
    require(archived == (PAPER / name).read_bytes(), f'Reviewed certificate changed: {name}')

result = {
    'all_checks_passed': True,
    'module_count': entry['module_count'],
    'declaration_count': entry['declaration_count'],
    'all_compiled_source_hashes_match': True,
    'git_checkout_crlf_normalized_files': checkout_line_endings,
    'compiled_module_inventory_matches': True,
    'compiled_sources_match_commit_after_checkout_normalization': True,
    'manuscript_source_sha256': manuscript_hash,
    'manuscript_source_commit': manuscript_commit,
    'epigraph_callback_and_acknowledgments_unchanged': True,
    'derivative_certificate_checks': len(certificate['checks']),
    'derivative_certificate_source_hashes_match': True,
    'all_release_references': tag,
    'reviewed_certificate_files_identical': len(certificate_files),
    'reviewed_certificate_commit': reviewed,
    'journal_pages': metadata['journal_pages'],
    'extended_pages': metadata['arxiv_pages'],
}
(HERE / 'final-state.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
