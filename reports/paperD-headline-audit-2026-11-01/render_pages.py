"""Render the title, revised claims and new proof pages for visual inspection."""
from pathlib import Path
import json
import re
import pypdfium2 as pdfium

ROOT = Path(__file__).resolve().parents[2]
BUILD = ROOT / '.pdf-build/paperD-headline-audit-2026-11-01'
HERE = Path(__file__).resolve().parent
OUT = HERE / 'rendered'
OUT.mkdir(exist_ok=True)
labels = {
    'problem131_memory': ['thm:threshold', 'thm:biased-limit-modes',
                         'prop:dominant-half', 'lem:weak-shape-transfer', 'sec:verify', 'app:threshold'],
    'problem131_arxiv': ['or:transition-unique', 'lem:thr-parameter-tail',
                        'eq:thr-final-derivatives'],
}
record = {}
for stem, targets in labels.items():
    aux = (BUILD / f'{stem}.aux').read_text(encoding='utf-8')
    selected = {1, 2} if stem == 'problem131_memory' else set()
    found = {}
    for label in targets:
        match = re.search(r'\\newlabel\{' + re.escape(label) + r'\}\{\{[^}]+\}\{(\d+)\}', aux)
        if match is None:
            raise RuntimeError(f'Missing label: {label}')
        page = int(match.group(1))
        found[label] = page
        selected.add(page)
        if label in ('thm:biased-limit-modes', 'or:transition-unique', 'sec:verify', 'lem:weak-shape-transfer'):
            selected.add(page + 1)
    document = pdfium.PdfDocument(BUILD / f'{stem}.pdf')
    for number in sorted(selected):
        page = document[number - 1]
        bitmap = page.render(scale=1.5)
        bitmap.to_pil().save(OUT / f'{stem}-{number}.png')
        bitmap.close()
        page.close()
    record[stem] = {'pages': len(document), 'label_pages': found,
                    'rendered_pages': sorted(selected)}
    document.close()
(HERE / 'rendered-pages.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
