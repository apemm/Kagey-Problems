"""Check of the threshold boards at heights 4, 5, 6 quoted from the paper (jis/pemmasani_jis.tex),
and of the earlier collar boards at heights 8 and 9 (2026-11-07/data)."""
import json
from boards import HERE, D07
from rectlib import check_board, parse_word

out = []


def add(name, h, cols, note):
    r = check_board(h, cols)
    q = h * h // 4
    r.update(name=name, note=note, doubles=sum(len(c) == 2 for c in cols),
             equality=r['black'] == len(cols) + q)
    out.append(r)
    print(name, r['width'], r['black'], r['valid'], r['equality'])


for m in range(6, 13):
    cols = [[] for _ in range(m)]
    for i in range(2, m):
        cols[i - 1].append(1)
    for c, r in ((m - 1, 2), (m, 2), (1, 3), (2, 3), (1, 4), (m, 4)):
        cols[c - 1].append(r)
    add(f'h4_w{m}', 4, [sorted(c) for c in cols], 'four-row family of the paper')
s8 = parse_word('14,45,25,5,5,34,23,12')
for extra in range(0, 6):
    add(f'h5_w{8 + extra}', 5, s8 + [[1]] * extra, 'S_8 followed by row-1 columns; 5 extra columns is the collar test')
add('h6_w15', 6, parse_word('56,45,34,23,1,1,14,1,1,12,36,1,25,6,16'), 'six-row board at width 15')
for f in ('sp_h8_g2_L13_R13_p1357_none_11', 'sp_h9_g2_L17_R17_p2468_none_11'):
    d = json.loads((D07 / f'{f}.json').read_text())
    add(f, d['h'], parse_word(d['word']), 'collar board of 2026-11-07 (pads on both sides)')
(HERE / 'verify_small.json').write_text(json.dumps(out, indent=1))
