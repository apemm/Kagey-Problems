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
for stem in ('problem131_memory', 'problem131_arxiv'):
    log = (BUILD / f'{stem}.log').read_text(errors='replace')
    for bad in ('undefined references', 'undefined citations', 'Overfull', '! LaTeX Error'):
        if bad in log:
            raise RuntimeError(f'{stem}: {bad}')
    pdf = BUILD / f'{stem}.pdf'
    counts[stem] = len(PdfReader(pdf).pages)
    shutil.copy2(pdf, PAPER / pdf.name)

aux = (BUILD / 'problem131_arxiv.aux').read_text()
match = re.search(r'\\newlabel\{or:threshold\}\{\{S6\}\{(\d+)\}', aux)
if match is None:
    raise RuntimeError('Section S6 page not found')
start = int(match.group(1)) - 1
reader = PdfReader(PAPER / 'problem131_arxiv.pdf')
writer = PdfWriter()
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
         PAPER / 'figures/family.pdf', PAPER / 'figures/shape.pdf']
relative = [p.relative_to(PAPER).as_posix() for p in files]
assert len(relative) == len(set(relative))
assert 'figures/crossing.pdf' not in relative
clean = ROOT / '.pdf-build/paperD-clean-arxiv-2026-11-01'
clean.mkdir(parents=True, exist_ok=True)
for p in files:
    dest = clean / p.relative_to(PAPER)
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(p, dest)
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
    'review_extract_pages': len(reader.pages) - start,
    'review_extract_original_pages': [start + 1, len(reader.pages)],
}
if len(abstract) >= 1920:
    raise RuntimeError(f'Abstract is {len(abstract)} characters; shorten before packaging')
(PAPER / 'arxiv_metadata.json').write_text(json.dumps(metadata, indent=2) + '\n', encoding='utf-8')
manifest = {'metadata': metadata, 'arxiv_upload_files': relative,
            'sha256': {name: digest(PAPER / name) for name in relative},
            'pdf_sha256': {name: digest(PAPER / name) for name in
                           ('problem131_memory.pdf', 'problem131_arxiv.pdf', 'threshold_proofs_review.pdf')}}
(OUT / 'delivery-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8')

print(json.dumps({'pages': counts, 'review_pages': metadata['review_extract_pages'],
                  'abstract_characters': len(abstract), 'upload_files': len(files),
                  'clean_build_source': str(clean)}, indent=2))
