"""Build the self-contained EJP and arXiv packages and check them in isolation."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import zipfile
from pypdf import PdfReader
import pypdfium2 as pdfium

P = Path(__file__).resolve().parent
ROOT = P.parents[2]
HERE = P / 'verification'
LEAN = ROOT / 'kagey-problems/problem131/lean'
BUILD = ROOT / '.pdf-build/paperD-submission'
TAG = 'paperD-ejp-v3'
TITLE = 'The bias interval of the elephant random walk'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--package-only', action='store_true',
                    help='Reuse PDFs only when their hashes and all source hashes match the manifest.')
args = parser.parse_args()


def require(value, message):
    if not value:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def digest_lf(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n', b'\n')).hexdigest()


inputs = []


def flatten(path):
    require(path not in inputs, f'Repeated or recursive input: {path}')
    inputs.append(path)
    source = path.read_text(encoding='utf-8')
    return re.sub(r'\\input\{([^}]+)\}', lambda m: flatten(
        path.parent / (m[1] if m[1].endswith('.tex') else m[1]+'.tex')).rstrip('\n'), source)


def build(directory, stem):
    if args.package_only:
        shutil.copy2(P/(stem+'.pdf'), directory/(stem+'.pdf'))
        return directory/(stem+'.pdf')
    for n in range(3):
        result = subprocess.run(['pdflatex', '-interaction=nonstopmode',
                                 '-halt-on-error', stem+'.tex'], cwd=directory,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (directory/f'pass{n+1}.txt').write_bytes(result.stdout)
        require(result.returncode == 0, f'Failed TeX build: {directory}')
    log = (directory/(stem+'.log')).read_text(errors='replace')
    for bad in ['undefined references', 'undefined citations', 'Overfull',
                '! LaTeX Error', 'Label(s) may have changed', 'does not exist']:
        require(bad not in log, f'{stem}: {bad}')
    return directory/(stem+'.pdf')


def archive(path, pairs):
    with zipfile.ZipFile(path, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for source, name in sorted(pairs, key=lambda v: v[1]):
            z.write(source, name)
    with zipfile.ZipFile(path) as z:
        require(z.testzip() is None, f'Bad archive: {path}')


source = flatten(P/'problem131_memory.tex')
disclosure = source.split(r'\section*{A note on the use of AI}',1)[1].split(
    r'\section*{Code and data}',1)[0].strip()
require(hashlib.sha256(disclosure.encode()).hexdigest() == '84c4b1f8d8f9e6d647d5f1ce43d77c64b2bdb197af29e0eef7c0256c95e82ed6',
        'The protected disclosure differs from the pinned text')
baseline = (P/'archive/combined-2026-11-06/sec_intro.tex').read_text(encoding='utf-8')
epigraph = lambda s: s.split(r'\noindent\begin{minipage}',1)[1].split(r'\end{minipage}',1)[0]
require(epigraph(source) == epigraph(baseline), 'The protected epigraph changed')
require(not any(ord(c)<32 and c not in '\n\r' for c in source), 'Control character in manuscript')
require('Online Resource' not in source and 'Statements and Declarations' not in source,
        'Obsolete journal matter remains')

figures = [P/'figures/phase.pdf']
figure_count = source.count(r'\begin{figure}')
arxiv_sources = [P/'problem131_arxiv.tex', P/'00README.json', P/'ejpecp.cls', *inputs, *figures]
ejp = BUILD/'ejp'
arxiv = BUILD/'arxiv'
for folder in [ejp,arxiv]:
    folder.mkdir(parents=True,exist_ok=True)
    (folder/'figures').mkdir(exist_ok=True)
for path in arxiv_sources:
    shutil.copy2(path,arxiv/path.relative_to(P))
ejp_sources = [P/'ejpecp.cls', *inputs, *figures]
for path in ejp_sources:
    shutil.copy2(path,ejp/path.relative_to(P))

if args.package_only:
    previous=json.loads((HERE/'delivery-manifest.json').read_text())
    for path in arxiv_sources:
        name=path.relative_to(P).as_posix()
        require(digest(path)==previous['input_sources'].get(name) or
                (name in previous.get('input_sources_lf', {}) and
                 digest_lf(path)==previous['input_sources_lf'][name]),
                f'Source changed; run a full build: {name}')
    for name in ['problem131_memory.pdf','problem131_arxiv.pdf']:
        require(digest(P/name)==previous['deliverables'][name]['sha256'],
                f'PDF changed; run a full build: {name}')
print('Checking and packaging existing PDFs' if args.package_only else
      'Building isolated EJP and arXiv sources',flush=True)
ejp_pdf=build(ejp,'problem131_memory')
arxiv_pdf=build(arxiv,'problem131_arxiv')
ejp_reader,arxiv_reader=PdfReader(ejp_pdf),PdfReader(arxiv_pdf)
texts=lambda reader: [' '.join(p.extract_text().split()) for p in reader.pages]
require(texts(ejp_reader)==texts(arxiv_reader),'Journal and arXiv text differs')
shutil.copy2(ejp_pdf,P/'problem131_memory.pdf')
shutil.copy2(arxiv_pdf,P/'problem131_arxiv.pdf')

abstract = source.split(r'\ABSTRACT{',1)[1].split(r'\begin{document}',1)[0].rstrip().removesuffix('}')
metadata={'title':TITLE,'author':'Arjun Pemmasani','primary_category':'math.PR',
          'cross_list':'cond-mat.stat-mech','abstract':abstract,
          'comments':f'{len(ejp_reader.pages)} pages, {figure_count} figures; complete proofs and verification records; repository tag {TAG}.',
          'journal_pages':len(ejp_reader.pages),'arxiv_pages':len(arxiv_reader.pages),
          'license_suggestion':'arXiv.org perpetual, non-exclusive license'}
(P/'arxiv_metadata.json').write_text(json.dumps(metadata,indent=2)+'\n',encoding='utf-8')

verification=json.loads((HERE/'verification-manifest.json').read_text())
require(verification.get('all_checks_passed') is True, 'Lean audit is not complete')
checked_modules=verification['libraries']['PaperD']['modules']
for module in checked_modules:
    require(digest(LEAN/module['file']) == module['sha256'] or
            digest_lf(LEAN/module['file']) == module.get('sha256_lf'),
            f"Lean source differs from audited source: {module['file']}")
require({m['file'] for m in checked_modules} ==
        {p.relative_to(LEAN).as_posix() for p in (LEAN/'PaperD').rglob('*.lean')} |
        {'PaperD.lean'}, 'Lean source inventory differs from audit')
verification_pairs=[]
for f in sorted(P.glob('*.py')):
    if f.name == 'build_submission.py': continue
    verification_pairs.append((f,'paperD/'+f.name))
for f in sorted((P/'data').glob('*')):
    if f.is_file(): verification_pairs.append((f,'paperD/data/'+f.name))
for f in sorted((LEAN/'PaperD').rglob('*.lean')):
    verification_pairs.append((f,'lean/'+f.relative_to(LEAN).as_posix()))
for name in ['PaperD.lean','lean-toolchain','lake-manifest.json','verify_lean.py']:
    f=LEAN/name
    if f.exists(): verification_pairs.append((f,'lean/'+name))
verification_pairs.append((LEAN/'PaperD/MAP.md','lean/PaperD/MAP.md'))
verification_pairs.append((LEAN/'PaperD/coverage_tables.tex','lean/PaperD/coverage_tables.tex'))
verification_pairs.append((HERE/'archive-lakefile.toml','lean/lakefile.toml'))
verification_pairs.append((HERE/'archive-README.md','README.md'))
verification_pairs.append((P/'README.md','paperD/README.md'))
verification_pairs.append((ROOT/'LICENSE','LICENSE'))
verification_pairs.append((P/'figures/make_phase_figure.py','paperD/figures/make_phase_figure.py'))
verification_pairs.extend((f,'paperD/figures/'+f.name) for f in figures)
for name in ['verification-manifest.json','build-log.txt','run_verification.py','README.md']:
    f=HERE/name
    if f.exists():verification_pairs.append((f,'paperD/verification/'+name))
archive(P/'paperD_verification_archive.zip',verification_pairs)

archive(P/'paperD_arxiv_source.zip',[(f,f.relative_to(P).as_posix()) for f in arxiv_sources])
ejp_pairs=[(ejp_pdf,'problem131_memory.pdf'),(P/'cover_letter.md','cover_letter.md'),
           (P/'README.md','README.md'),(P/'submission_notes.md','submission_notes.md'),
           (P/'paperD_verification_archive.zip','paperD_verification_archive.zip')]
ejp_pairs.extend((f,f.relative_to(P).as_posix()) for f in ejp_sources)
archive(P/'paperD_ejp_submission.zip',ejp_pairs)

rendered=BUILD/'rendered'
rendered.mkdir(exist_ok=True)
doc=pdfium.PdfDocument(str(ejp_pdf))
for page in sorted({p for p in [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,28,29,len(doc)-1]
                    if 0 <= p < len(doc)}):
    doc[page].render(scale=1.5).to_pil().save(rendered/f'page-{page+1:02d}.png')
deliverables=[P/n for n in ['problem131_memory.pdf','problem131_arxiv.pdf',
                           'paperD_arxiv_source.zip','paperD_ejp_submission.zip',
                           'paperD_verification_archive.zip','arxiv_metadata.json']]
manifest={'tag':TAG,'pages':len(ejp_reader.pages),'figures':figure_count,
          'isolated_builds':'passed, three passes each; extracted PDF text identical',
          'pdf_validation':('reused PDFs after checking all source and PDF hashes' if args.package_only
                            else 'rebuilt both PDFs in isolation'),
          'disclosure':'matches the pinned text',
          'epigraph':'unchanged',
          'latex_warning':'official class sets the already-loaded pagebackref option; informational only',
          'input_sources':{f.relative_to(P).as_posix():digest(f) for f in arxiv_sources},
          'input_sources_lf':{f.relative_to(P).as_posix():digest_lf(f) for f in arxiv_sources
                              if f.suffix in {'.tex','.cls','.json'}},
          'deliverables':{f.relative_to(P).as_posix():{'bytes':f.stat().st_size,'sha256':digest(f)} for f in deliverables}}
(HERE/'delivery-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'pages':len(ejp_reader.pages),
                  'pdfs':'VERIFIED EXISTING BUILDS' if args.package_only else 'ISOLATED BUILDS PASSED',
                  'archives':'PASS','disclosure':'UNCHANGED'},indent=2))
