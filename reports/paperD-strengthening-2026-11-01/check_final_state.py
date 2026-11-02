"""Check proof-source hashes, disclosure preservation and release references."""
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
changed = [m['file'] for m in entry['modules']
           if hashlib.sha256((LEAN / m['file']).read_bytes()).hexdigest() != m['sha256']]
require(not changed, f'Sources changed after the Lean audit: {changed}')

tex = (PAPER / 'problem131_memory.tex').read_text(encoding='utf-8')
start = tex.index(r'\section*{A note on the use of AI}')
end = tex.index(r'\section*{Statements and Declarations}')
disclosure_hash = hashlib.sha256(tex[start:end].encode()).hexdigest()
require(disclosure_hash == 'ed20652c6d4be4b2b4eab60960d73bbd0a1b1487f596bd7a8de6fb506288593d',
        'The disclosure changed')

metadata = json.loads((PAPER / 'arxiv_metadata.json').read_text())
tag = 'paperD-arxiv-v1'
for section in ('Data availability.', 'Code availability.'):
    part = tex.split(r'\paragraph{' + section + '}', 1)[1].split(r'\paragraph{', 1)[0]
    refs = re.findall(r'github\.com/apemm/Kagey-Problems/tree/([^/}]+)', part)
    require(refs and set(refs) == {tag}, f'Incorrect release reference in {section}: {refs}')
require(f'tag {tag}' in metadata['comments'], 'Metadata has the wrong release reference')
require(tag in (PAPER / 'README.md').read_text(encoding='utf-8'), 'README lacks the release reference')

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
    'unchanged_disclosure_sha256': disclosure_hash,
    'all_release_references': tag,
    'reviewed_certificate_files_identical': len(certificate_files),
    'reviewed_certificate_commit': reviewed,
    'journal_pages': metadata['journal_pages'],
    'extended_pages': metadata['arxiv_pages'],
}
(HERE / 'final-state.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
