"""Check the final Paper D PDFs, citation sets, and exact upload source set."""
import sys

if sys.flags.optimize:
    raise RuntimeError('Run without -O or -OO: PDF and archive validation requires assertions')

from pathlib import Path
import hashlib
import json
import re
import subprocess
import zipfile
from pypdf import PdfReader

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / 'kagey-problems/problem131/paperD'
BUILD = ROOT / '.pdf-build/paperD-final-audit-2026-11-02'
CLEAN = ROOT / '.pdf-build/paperD-final-clean-2026-11-02/build'
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


def check_links(reader):
    internal, companion = 0, 0
    for page in reader.pages:
        for ref in page.get('/Annots', []):
            annotation = ref.get_object()
            action = annotation.get('/A', {})
            target = annotation.get('/Dest')
            if action.get('/S') == '/GoTo':
                target = action.get('/D')
            if isinstance(target, str):
                assert target in reader.named_destinations, target
                dest = reader.named_destinations[target]
                assert 0 <= reader.get_destination_page_number(dest) < len(reader.pages)
                internal += 1
            if action.get('/S') == '/GoToR':
                assert action['/F'] == 'problem131_arxiv.pdf'
                complete = PdfReader(PAPER / action['/F'])
                assert action['/D'] in complete.named_destinations
                companion += 1
    return {'internal': internal, 'companion': companion, 'all_targets_resolve': True}


results = {}
for name in ('problem131_memory.pdf', 'problem131_arxiv.pdf', 'threshold_proofs_review.pdf'):
    reader = PdfReader(PAPER / name)
    results[name] = {'pages': len(reader.pages), 'fonts': font_inventory(reader),
                     'links': check_links(reader),
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
    assert archive.testzip() is None
    assert len(archive.namelist()) == len(set(archive.namelist()))
    assert set(archive.namelist()) == set(manifest['arxiv_upload_files'])
    for name in archive.namelist():
        assert archive.read(name) == (PAPER / name).read_bytes()
with zipfile.ZipFile(PAPER / 'paperD_jtp_submission.zip') as archive:
    assert archive.testzip() is None
    assert len(archive.namelist()) == len(set(archive.namelist()))
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

source = (PAPER / 'problem131_memory.tex').read_text(encoding='utf-8')
baseline = subprocess.check_output(
    ['git', 'show', 'de1f05b17283af605cfd46c93e9b331baec8f593:'
     'kagey-problems/problem131/paperD/problem131_memory.tex'], cwd=ROOT).decode('utf-8')
assert source == baseline.replace('\r\n', '\n')
scientific_paths = ['kagey-problems/problem131/lean',
                    'kagey-problems/problem131/verify_all.py',
                    'kagey-problems/problem131/paperD/data',
                    ':(glob)kagey-problems/problem131/paperD/*.py']
subprocess.run(['git', 'diff', '--exit-code', 'paperD-arxiv-v3', '--',
                *scientific_paths], cwd=ROOT, check=True)
assert subprocess.check_output(['git', 'rev-parse', 'paperD-arxiv-v3^{commit}'],
                               cwd=ROOT).decode().strip() == '9d0f4ba4995c7ec423a70463e5136056492d365c'
metadata = json.loads((PAPER / 'arxiv_metadata.json').read_text())
abstract = ' '.join(re.search(r'\\begin\{abstract\}(.*?)\\end\{abstract\}',
                             source, re.S).group(1).split())
assert metadata['abstract'] == abstract
assert metadata['abstract_characters'] == len(abstract) < 1920
for key, name in [('journal_pages', 'problem131_memory.pdf'),
                  ('arxiv_pages', 'problem131_arxiv.pdf'),
                  ('review_extract_pages', 'threshold_proofs_review.pdf')]:
    assert metadata[key] == results[name]['pages']
cover = (PAPER / 'cover_letter.md').read_text(encoding='utf-8')
assert not any(mark in cover for mark in ('$', '\\', '`'))
assert 'a* ≈ 0.6688128600146' in cover
assert 'unanimity in a specified color' in cover
settings = json.loads((PAPER / '00README.json').read_text())
assert settings['spec_version'] == 1
assert settings['process']['compiler'] == 'pdflatex'
assert settings['sources'] == [
    {'filename': 'problem131_arxiv.tex', 'usage': 'toplevel'},
    {'filename': 'problem131_memory.tex', 'usage': 'include'}]
results['source_consistency'] = {
    'entry_source_unchanged_from_baseline': True,
    'scientific_sources_unchanged_from_v3': True,
    'v3_tag_unchanged': True, 'metadata_matches': True,
    'cover_letter_plain_text': True, 'arxiv_compiler_settings_checked': True}
(OUT / 'pdf-checks.json').write_text(json.dumps(results, indent=2) + '\n', encoding='utf-8')
print(json.dumps({key: value.get('pages', value) for key, value in results.items()}, indent=2))
