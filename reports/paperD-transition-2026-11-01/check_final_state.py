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
disclosure_commit = '39030b9427f0fb83292bf38a8904021d34dfc3b0'
require(disclosure_hash == '53368740b012a9705eb55400a6c6fd91ee56737ead10456cebe4201e3935014d',
        'The disclosure changed')
user_source = subprocess.check_output(
    ['git', 'show', f'{disclosure_commit}:kagey-problems/problem131/paperD/problem131_memory.tex'],
    cwd=ROOT).decode('utf-8').replace('\r\n', '\n')
user_start = user_source.index(r'\section*{A note on the use of AI}')
user_end = user_source.index(r'\section*{Statements and Declarations}')
require(tex[start:end] == user_source[user_start:user_end],
        'The disclosure differs from the author revision')

metadata = json.loads((PAPER / 'arxiv_metadata.json').read_text())
tag = 'paperD-arxiv-v2'
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
    'unchanged_disclosure_sha256': disclosure_hash,
    'disclosure_author_source_commit': disclosure_commit,
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
