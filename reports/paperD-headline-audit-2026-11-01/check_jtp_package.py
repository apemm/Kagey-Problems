"""Check the final Paper D PDFs, citation sets, and exact upload source set."""
import sys

if sys.flags.optimize:
    raise RuntimeError('Run without -O or -OO: PDF and archive validation requires assertions')

from pathlib import Path
import hashlib
import json
import re
import zipfile
from pypdf import PdfReader

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / 'kagey-problems/problem131/paperD'
BUILD = ROOT / '.pdf-build/paperD-headline-audit-2026-11-01'
CLEAN = ROOT / '.pdf-build/paperD-headline-clean-2026-11-01/build'
OUT = Path(__file__).resolve().parent


def font_inventory(reader):
    fonts = {}
    seen = set()

    def resources(value):
        if value is None:
            return
        obj = value.get_object()
        identity = id(obj)
        if identity in seen:
            return
        seen.add(identity)
        for ref in obj.get('/Font', {}).get_object().values() if '/Font' in obj else []:
            font = ref.get_object()
            children = font.get('/DescendantFonts', [font])
            embedded = all(any(key in child.get_object().get('/FontDescriptor', {}).get_object()
                               for key in ('/FontFile', '/FontFile2', '/FontFile3'))
                           for child in children)
            fonts[str(font.get('/BaseFont'))] = {
                'subtype': str(font.get('/Subtype')), 'embedded': embedded}
        for ref in obj.get('/XObject', {}).get_object().values() if '/XObject' in obj else []:
            resources(ref.get_object().get('/Resources'))

    for page in reader.pages:
        resources(page.get('/Resources'))
    assert fonts
    assert all(f['embedded'] and f['subtype'] != '/Type3' for f in fonts.values())
    return fonts


results = {}
for name in ('problem131_memory.pdf', 'problem131_arxiv.pdf', 'threshold_proofs_review.pdf'):
    reader = PdfReader(PAPER / name)
    results[name] = {'pages': len(reader.pages), 'fonts': font_inventory(reader),
                     'sha256': hashlib.sha256((PAPER / name).read_bytes()).hexdigest()}

for stem in ('problem131_memory', 'problem131_arxiv'):
    published = PdfReader(PAPER / f'{stem}.pdf')
    isolated = PdfReader(CLEAN / f'{stem}.pdf')
    assert [p.extract_text() for p in published.pages] == [p.extract_text() for p in isolated.pages]
    for folder in (BUILD, CLEAN):
        aux = (folder / f'{stem}.aux').read_text()
        citations = {key for group in re.findall(r'\\citation\{([^}]+)\}', aux)
                     for key in group.split(',')}
        bibliography = set(re.findall(r'\\bibcite\{([^}]+)\}', aux))
        assert citations == bibliography, (stem, citations - bibliography, bibliography - citations)
        log = (folder / f'{stem}.log').read_text(errors='replace')
        for bad in ('undefined references', 'undefined citations', 'Overfull', '! LaTeX Error'):
            assert bad not in log, (stem, bad)
    results[f'{stem}.pdf']['isolated_build_text_matches'] = True
    results[f'{stem}.pdf']['all_bibliography_entries_cited'] = True

main = PdfReader(PAPER / 'problem131_memory.pdf')
assert 'Acknowledgments' in main.pages[0].extract_text()
assert 'Corresponding author:' in main.pages[0].extract_text()
assert '1 Introduction' in main.pages[1].extract_text()
assert 'a riddle my Indian mother told me' in main.pages[1].extract_text()

manifest = json.loads((OUT / 'delivery-manifest.json').read_text())
with zipfile.ZipFile(PAPER / 'paperD_arxiv_source.zip') as archive:
    assert set(archive.namelist()) == set(manifest['arxiv_upload_files'])
    for name in archive.namelist():
        assert archive.read(name) == (PAPER / name).read_bytes()
with zipfile.ZipFile(PAPER / 'paperD_jtp_submission.zip') as archive:
    assert set(archive.namelist()) == set(manifest['jtp_submission_files'])
    for name in archive.namelist():
        assert archive.read(name) == (PAPER / name).read_bytes()

extended = PdfReader(PAPER / 'problem131_arxiv.pdf')
review = PdfReader(PAPER / 'threshold_proofs_review.pdf')
start, end = manifest['metadata']['review_extract_original_pages']
assert [p.extract_text() for p in review.pages[1:]] == [
    p.extract_text() for p in extended.pages[start - 1:end]]
results['packages'] = {'arxiv_files': len(manifest['arxiv_upload_files']),
                       'jtp_files': len(manifest['jtp_submission_files']),
                       'all_packaged_bytes_match': True, 'review_extract_matches': True}
(OUT / 'pdf-checks.json').write_text(json.dumps(results, indent=2) + '\n', encoding='utf-8')
print(json.dumps({key: value.get('pages', value) for key, value in results.items()}, indent=2))
