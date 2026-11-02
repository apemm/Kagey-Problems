"""Render the pages affected by the posting corrections."""
from pathlib import Path
import json
import re
import pypdfium2 as pdfium

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
BUILD = ROOT / '.pdf-build/paperD-posting-corrections-2026-11-02'
PAPER = ROOT / 'kagey-problems/problem131/paperD'
OUT = HERE / 'rendered'
OUT.mkdir(exist_ok=True)

labels = ['thm:main-shape', 'sec:prior', 'sec:organization', 'fig:family',
          'fig:shape', 'prop:odd', 'thm:biased-limit-modes',
          'prop:all-bias-modes', 'prop:dominant-half', 'sec:verify']
aux = (BUILD / 'problem131_memory.aux').read_text()
pages = {1, 2, 28}
locations = {}
for label in labels:
    match = re.search(r'\\newlabel\{' + re.escape(label) + r'\}\{\{[^}]+\}\{(\d+)\}', aux)
    if match is None:
        raise RuntimeError('Missing label: ' + label)
    number = int(match.group(1))
    locations[label] = number
    pages.add(number)
    if label in ('sec:prior', 'prop:all-bias-modes', 'sec:verify'):
        pages.add(number + 1)
record = {}
for stem, selected in [('problem131_memory', sorted(pages)),
                       ('problem131_arxiv', [1])]:
    doc = pdfium.PdfDocument(PAPER / (stem + '.pdf'))
    for number in selected:
        page = doc[number - 1]
        bitmap = page.render(scale=1.3)
        bitmap.to_pil().save(OUT / f'{stem}-{number}.png')
        bitmap.close()
        page.close()
    record[stem] = {'pages': len(doc), 'rendered_pages': selected}
    doc.close()
record['label_pages'] = locations
(HERE / 'rendered-pages.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
