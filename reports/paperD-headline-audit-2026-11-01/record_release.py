"""Join the completed numerical, formal and package checks for the source tag."""
from pathlib import Path
import hashlib
import json
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
PAPER = ROOT / 'kagey-problems/problem131/paperD'
num = json.loads((HERE / 'release-numerical-verification.json').read_text())
lean = json.loads((HERE / 'release-lean-verification.json').read_text())
final = json.loads((HERE / 'final-state.json').read_text())
pdf = json.loads((HERE / 'pdf-checks.json').read_text())
source = num['source_commit']
if source != lean['source_commit']:
    raise RuntimeError('Numerical and formal records name different source commits')
if source != final['manuscript_source_commit']:
    raise RuntimeError('The manuscript check names a different source commit')
if not all(x['all_checks_passed'] for x in (num, lean, final)):
    raise RuntimeError('A release check failed')
delivery = json.loads((HERE / 'delivery-manifest.json').read_text())
if delivery['metadata'] != json.loads((PAPER / 'arxiv_metadata.json').read_text()):
    raise RuntimeError('The delivery metadata is stale')
for name, digest in {**delivery['sha256'], **delivery['pdf_sha256']}.items():
    if hashlib.sha256((PAPER / name).read_bytes()).hexdigest() != digest:
        raise RuntimeError(f'The delivery manifest is stale: {name}')
for name in ('problem131_memory.pdf', 'problem131_arxiv.pdf', 'threshold_proofs_review.pdf'):
    if pdf[name]['sha256'] != delivery['pdf_sha256'][name]:
        raise RuntimeError(f'The PDF verification is stale: {name}')
    if not all(font['embedded'] and font['subtype'] != '/Type3'
               for font in pdf[name]['fonts'].values()) or not pdf[name]['fonts']:
        raise RuntimeError(f'Font verification failed: {name}')
for name in ('problem131_memory.pdf', 'problem131_arxiv.pdf'):
    if not (pdf[name]['isolated_build_text_matches'] and
            pdf[name]['all_bibliography_entries_cited']):
        raise RuntimeError(f'The isolated PDF verification did not pass: {name}')
if not (pdf['packages']['all_packaged_bytes_match'] and
        pdf['packages']['review_extract_matches']):
    raise RuntimeError('The package verification did not pass')
archive_hashes = {}
for name, inventory in (('paperD_arxiv_source.zip', 'arxiv_upload_files'),
                        ('paperD_jtp_submission.zip', 'jtp_submission_files')):
    path = PAPER / name
    archive_hashes[name] = hashlib.sha256(path.read_bytes()).hexdigest()
    with zipfile.ZipFile(path) as package:
        members = package.namelist()
        if len(members) != len(set(members)) or set(members) != set(delivery[inventory]):
            raise RuntimeError(f'The package inventory changed: {name}')
        for member in members:
            if package.read(member) != (PAPER / member).read_bytes():
                raise RuntimeError(f'The package source changed: {name}: {member}')
if archive_hashes['paperD_jtp_submission.zip'] != delivery['jtp_submission_sha256']:
    raise RuntimeError('The journal package hash changed')
fresh_path = (Path(num['export_directory']) /
              'kagey-problems/problem131/paperD/data/transition_derivative_certificate.json')
fresh_bytes = fresh_path.read_bytes()
fresh = json.loads(fresh_bytes)
adopted = json.loads((ROOT /
    'kagey-problems/problem131/paperD/data/transition_derivative_certificate.json').read_text())
if not (fresh['all_checks_passed'] and all(fresh['checks'].values()) and
        len(fresh['checks']) == final['derivative_certificate_checks'] and
        fresh['adopted_bounds'] == adopted['adopted_bounds'] and
        fresh['source_sha256'] == adopted['source_sha256']):
    raise RuntimeError('The fresh derivative certificate differs from the adopted certificate')
(HERE / 'release-transition-derivative-certificate.json').write_bytes(fresh_bytes)
for name, expected in (
    ('release-numerical-verification.txt', num['log_sha256']),
    ('release-lean-build.txt', lean['build_log_sha256']),
    ('verification-manifest.json', lean['full_axiom_audit_sha256']),
):
    if hashlib.sha256((HERE / name).read_bytes()).hexdigest() != expected:
        raise RuntimeError(f'Changed verification evidence: {name}')
# Scientific sources and archived packages stay fixed; editorial guides may evolve.
subprocess.run(['git', 'diff', '--exit-code', source, '--',
                'kagey-problems/problem131/paperD',
                'kagey-problems/problem131/lean',
                ':(exclude)kagey-problems/problem131/paperD/README.md'],
               cwd=ROOT, check=True)
v1 = subprocess.check_output(
    ['git', 'rev-parse', 'paperD-arxiv-v1^{commit}'], cwd=ROOT, text=True).strip()
if v1 != '7e78cbad17b2dc60101363d09275e0ee5067c4d5':
    raise RuntimeError('The earlier release tag moved')
v2 = subprocess.check_output(['git', 'rev-parse', 'paperD-arxiv-v2^{commit}'], cwd=ROOT, text=True).strip()
if v2 != '8dfa2584f6acf9ea74c5b936946d321dde80224e':
    raise RuntimeError('The second release tag moved')
record = {
    'all_checks_passed': True,
    'tag': 'paperD-arxiv-v3',
    'source_commit': source,
    'prior_tag': 'paperD-arxiv-v1',
    'prior_tag_commit_unchanged': v1,
    'second_tag_commit_unchanged': v2,
    'manuscript_source_commit': final['manuscript_source_commit'],
    'manuscript_source_sha256': final['manuscript_source_sha256'],
    'lean_modules': final['module_count'],
    'lean_declarations': final['declaration_count'],
    'numerical_scripts_passed': 7,
    'new_derivative_certificate_checks': final['derivative_certificate_checks'],
    'fresh_derivative_certificate_sha256': hashlib.sha256(fresh_bytes).hexdigest(),
    'numerical_scope': num['scope'],
    'journal_pages': pdf['problem131_memory.pdf']['pages'],
    'extended_pages': pdf['problem131_arxiv.pdf']['pages'],
    'review_extract_pages': pdf['threshold_proofs_review.pdf']['pages'],
    'package_checks': pdf['packages'],
    'archive_sha256': archive_hashes,
    'pdf_checks_sha256': hashlib.sha256((HERE / 'pdf-checks.json').read_bytes()).hexdigest(),
    'delivery_manifest_sha256': hashlib.sha256((HERE / 'delivery-manifest.json').read_bytes()).hexdigest(),
}
(HERE / 'release-verification.json').write_text(json.dumps(record, indent=2) + '\n')
readme = f'''# Verified Paper D source release

Tag `paperD-arxiv-v3` identifies source commit
[`{source[:12]}`](https://github.com/apemm/Kagey-Problems/tree/{source}).
The later evidence commit adds only verification records. The manuscript's
scientific sources and upload archives are those checked at the source commit.
The earlier `paperD-arxiv-v1` remains at `{v1[:12]}` and
`paperD-arxiv-v2` remains at `{v2[:12]}`.

The final source commit passed the seven-script numerical suite, including
the complete new transition-derivative certificate. The final Lean rebuild
passed and matches the complete {final['module_count']}-module,
{final['declaration_count']:,}-declaration axiom audit.
The numerical scope is stated in `release-verification.json`: the older
threshold records receive archived-record checks and three fresh probes,
not a repeat of all nine heavy jobs.

The journal PDF has {record['journal_pages']} pages, the extended PDF
{record['extended_pages']}, and the review extract {record['review_extract_pages']}.
Both archives passed isolated rebuild, citation, font and exact-file checks.
The manuscript matches the verified source commit. The epigraph, callback
and acknowledgments are unchanged.

The [verification guide](README.md) records the formalization boundaries.
Arb transcendental enclosures remain numerical. The characteristic-function
instantiation, holomorphic moment estimates and assembly of the uniform tail
bounds retain their written analytic proof. The
[direct review](../../research_notes/Paper%20D%20headline%20audit/primary_review.md)
records the mathematical checks and the scope of the source readings.

Nothing was submitted to a journal or arXiv, and no email was sent.
'''
(HERE / 'RELEASE.md').write_text(readme, encoding='utf-8', newline='\n')
print(json.dumps(record, indent=2))
