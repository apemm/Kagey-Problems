"""Join the completed numerical, formal and package checks for the source tag."""
from pathlib import Path
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
num = json.loads((HERE / 'release-numerical-verification.json').read_text())
lean = json.loads((HERE / 'release-lean-verification.json').read_text())
final = json.loads((HERE / 'final-state.json').read_text())
pdf = json.loads((HERE / 'pdf-checks.json').read_text())
source = num['source_commit']
if source != lean['source_commit']:
    raise RuntimeError('Numerical and formal records name different source commits')
if not all(x['all_checks_passed'] for x in (num, lean, final)):
    raise RuntimeError('A release check failed')
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
record = {
    'all_checks_passed': True,
    'tag': 'paperD-arxiv-v2',
    'source_commit': source,
    'prior_tag': 'paperD-arxiv-v1',
    'prior_tag_commit_unchanged': v1,
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
}
(HERE / 'release-verification.json').write_text(json.dumps(record, indent=2) + '\n')
readme = f'''# Verified Paper D source release

Tag `paperD-arxiv-v2` identifies source commit
[`{source[:12]}`](https://github.com/apemm/Kagey-Problems/tree/{source}).
The later evidence commit adds only verification records. The manuscript's
scientific sources and upload archives are those checked at the source commit.
The earlier `paperD-arxiv-v1` remains at `{v1[:12]}`.

The final source commit passed the seven-script numerical suite, including
the complete new transition-derivative certificate. The final Lean rebuild
passed and matches the complete 361-module, 23,841-declaration axiom audit.
The numerical scope is stated in `release-verification.json`: the older
threshold records receive archived-record checks and three fresh probes,
not a repeat of all nine heavy jobs.

The journal PDF has 51 pages, the extended PDF 72, and the review extract 9.
Both archives passed isolated rebuild, citation, font and exact-file checks.
The manuscript matches the verified source commit. The epigraph, callback
and acknowledgments are unchanged.

The [verification guide](README.md) records the formalization boundaries.
Arb transcendental enclosures and the detailed differentiated-smoothing
integral reduction remain numerical and written proofs, respectively.
The [research report](../Paper%20D%20transition%20closure.md) distinguishes
full readings, targeted checks and outstanding full texts.

Nothing was submitted to a journal or arXiv, and no email was sent.
'''
(HERE / 'RELEASE.md').write_text(readme, encoding='utf-8', newline='\n')
print(json.dumps(record, indent=2))
