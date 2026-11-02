"""Package the audited Paper D sources and reproduce the S6 review extract."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import zipfile
from pypdf import PdfReader, PdfWriter

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / 'kagey-problems/problem131/paperD'
BUILD = ROOT / '.pdf-build/paperD-audit-2026-11-01'
OUT = Path(__file__).resolve().parent
TITLE = 'Shape transitions and rare reversals in the elephant random walk'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

counts = {}
for stem in ('problem131_memory', 'problem131_arxiv', 'threshold_review_cover'):
    log = (BUILD / f'{stem}.log').read_text(errors='replace')
    for bad in ('undefined references', 'undefined citations', 'Overfull', '! LaTeX Error'):
        if bad in log:
            raise RuntimeError(f'{stem}: {bad}')
    pdf = BUILD / f'{stem}.pdf'
    counts[stem] = len(PdfReader(pdf).pages)
    if stem != 'threshold_review_cover':
        shutil.copy2(pdf, PAPER / pdf.name)

aux = (BUILD / 'problem131_arxiv.aux').read_text()
match = re.search(r'\\newlabel\{or:threshold\}\{\{S6\}\{(\d+)\}', aux)
if match is None:
    raise RuntimeError('Section S6 page not found')
start = int(match.group(1)) - 1
reader = PdfReader(PAPER / 'problem131_arxiv.pdf')
writer = PdfWriter()
cover = PdfReader(BUILD / 'threshold_review_cover.pdf')
assert len(cover.pages) == 1
writer.add_page(cover.pages[0])
# S6 starts on its own page. Include the bibliography so the extract is usable
# together with the journal manuscript without a separate reference list.
for page in reader.pages[start:]:
    writer.add_page(page)
writer.add_metadata({'/Title': TITLE + ' — threshold proofs for review',
                     '/Author': 'Arjun Pemmasani',
                     '/Subject': 'Section S6 and bibliography; review-only extract'})
review = PAPER / 'threshold_proofs_review.pdf'
with review.open('wb') as stream:
    writer.write(stream)

files = [PAPER / 'problem131_arxiv.tex', PAPER / 'problem131_memory.tex',
         *sorted(PAPER.glob('sec_*.tex')), *sorted(PAPER.glob('app_*.tex')),
         PAPER / 'or_family_proofs.tex', PAPER / 'online_resource_body.tex',
         PAPER / 'online_resource_bib.tex', PAPER / '00README.json',
         PAPER / 'figures/Fig1.pdf', PAPER / 'figures/Fig2.pdf']
relative = [p.relative_to(PAPER).as_posix() for p in files]
assert len(relative) == len(set(relative))
assert 'figures/crossing.pdf' not in relative
clean = ROOT / '.pdf-build/paperD-jtp-clean-2026-11-01'
clean.mkdir(parents=True, exist_ok=True)
for p in files:
    dest = clean / p.relative_to(PAPER)
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(p, dest)
actual = {p.relative_to(clean).as_posix() for p in clean.rglob('*')
          if p.is_file() and 'build' not in p.relative_to(clean).parts}
assert actual == set(relative), (actual - set(relative), set(relative) - actual)
with zipfile.ZipFile(PAPER / 'paperD_arxiv_source.zip', 'w', zipfile.ZIP_DEFLATED) as z:
    for p in files:
        z.write(p, p.relative_to(PAPER))

tex = (PAPER / 'problem131_memory.tex').read_text(encoding='utf-8')
abstract = re.search(r'\\begin\{abstract\}(.*?)\\end\{abstract\}', tex, re.S).group(1)
abstract = ' '.join(abstract.split())
metadata = {
    'title': TITLE, 'author': 'Arjun Pemmasani',
    'primary_category': 'math.PR', 'cross_list': 'cond-mat.stat-mech',
    'optional_cross_list': 'math.CO',
    'abstract': abstract, 'abstract_characters': len(abstract),
    'comments': f"{counts['problem131_arxiv']} pages, 2 figures; Sections S1-S6 extend the journal version; proof certificates and Lean source at github.com/apemm/Kagey-Problems, commit aa88996f.",
    'license_suggestion': 'arXiv.org perpetual, non-exclusive license',
    'journal_pages': counts['problem131_memory'],
    'arxiv_pages': counts['problem131_arxiv'],
    'review_extract_pages': 1 + len(reader.pages) - start,
    'review_cover_pages': 1,
    'review_extract_original_pages': [start + 1, len(reader.pages)],
}
if len(abstract) >= 1920:
    raise RuntimeError(f'Abstract is {len(abstract)} characters; shorten before packaging')
(PAPER / 'arxiv_metadata.json').write_text(json.dumps(metadata, indent=2) + '\n', encoding='utf-8')

jtp_readme = f'''# Paper D journal submission files

Target: Journal of Theoretical Probability. Prepared for author review; not submitted.

- Journal manuscript: problem131_memory.pdf ({counts['problem131_memory']} pages).
- Main editable source: problem131_memory.tex. Compile with pdflatex or latexmk -pdf.
- Extended reference file: problem131_arxiv.pdf ({counts['problem131_arxiv']} pages).
- Threshold proofs for peer review: threshold_proofs_review.pdf ({metadata['review_extract_pages']} pages, including an identification cover).
- Extended editable source: problem131_arxiv.tex.
- Supplement cover source: threshold_review_cover.tex.
- Vector figures: figures/Fig1.pdf and figures/Fig2.pdf; EPS versions are supplied too.
- Cover letter: cover_letter.md. Review its declarations before upload.
- Author checklist: submission_notes.md.

The journal source inputs the section and appendix files beside it. Its bibliography
is inline. The journal build does not require the extended PDF to compile. The
extended PDF and review-only extract supply the expanded threshold proofs referred
to by the journal manuscript. They are reference files for peer review, not proposed
publication supplements. No arXiv identifier has been assigned in these files.

Upload the editable source set and journal PDF using the submission system's file
categories. Identify the two additional PDFs as material for peer review. Complete
the system's author, contribution, funding, and competing-interest fields separately.
The original 00README.json is for arXiv only and is excluded from this package.
'''
(PAPER / 'JTP_PACKAGE_README.txt').write_text(jtp_readme, encoding='utf-8')
jtp_files = [p for p in files if p.name != '00README.json'] + [
    PAPER / name for name in ('problem131_memory.pdf', 'problem131_arxiv.pdf',
        'threshold_proofs_review.pdf', 'threshold_review_cover.tex',
        'figures/Fig1.eps', 'figures/Fig2.eps', 'cover_letter.md',
        'submission_notes.md', 'JTP_PACKAGE_README.txt')]
with zipfile.ZipFile(PAPER / 'paperD_jtp_submission.zip', 'w', zipfile.ZIP_DEFLATED) as z:
    for p in jtp_files:
        z.write(p, p.relative_to(PAPER))
manifest = {'metadata': metadata, 'arxiv_upload_files': relative,
            'jtp_submission_files': [p.relative_to(PAPER).as_posix() for p in jtp_files],
            'jtp_submission_sha256': digest(PAPER / 'paperD_jtp_submission.zip'),
            'sha256': {name: digest(PAPER / name) for name in relative},
            'pdf_sha256': {name: digest(PAPER / name) for name in
                           ('problem131_memory.pdf', 'problem131_arxiv.pdf', 'threshold_proofs_review.pdf')}}
(OUT / 'delivery-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8')

print(json.dumps({'pages': counts, 'review_pages': metadata['review_extract_pages'],
                  'abstract_characters': len(abstract), 'upload_files': len(files),
                  'clean_build_source': str(clean)}, indent=2))
