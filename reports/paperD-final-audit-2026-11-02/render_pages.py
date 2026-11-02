"""Render the corrected passages and the review extract for visual inspection."""
from pathlib import Path
import json
import re
import pypdfium2 as pdfium

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
BUILD = ROOT / '.pdf-build/paperD-final-audit-2026-11-02'
PAPER = ROOT / 'kagey-problems/problem131/paperD'
OUT = HERE / 'rendered'
OUT.mkdir(exist_ok=True)

def label_page(stem, label):
    aux = (BUILD / f'{stem}.aux').read_text()
    match = re.search(r'\\newlabel\{' + re.escape(label) + r'\}\{\{[^}]+\}\{(\d+)\}', aux)
    if match is None:
        raise RuntimeError('Missing label: ' + label)
    return int(match.group(1))

selected = {
    'problem131_memory': {1, 2, label_page('problem131_memory', 'app:shape'),
                          label_page('problem131_memory', 'cor:biased-near-one-peaks')},
    'problem131_arxiv': {label_page('problem131_arxiv', 'or:window'),
                         label_page('problem131_arxiv', 'prop:main-window')},
    'threshold_proofs_review': {1, 2},
}
record = {}
for stem, pages in selected.items():
    doc = pdfium.PdfDocument(PAPER / f'{stem}.pdf')
    for number in sorted(pages):
        page = doc[number - 1]
        bitmap = page.render(scale=1.5)
        bitmap.to_pil().save(OUT / f'{stem}-{number}.png')
        bitmap.close()
        page.close()
    record[stem] = {'pages': len(doc), 'rendered_pages': sorted(pages)}
    doc.close()
(HERE / 'rendered-pages.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
