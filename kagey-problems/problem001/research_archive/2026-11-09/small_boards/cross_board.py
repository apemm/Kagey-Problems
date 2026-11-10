"""Cross-height tests of the label order.

1. Rank correlation of the slot of a row pair in two boards, on the pairs they share,
   with the rows of the lower board shifted by 0, by half the height difference, and by
   the full height difference.
2. Restriction test: take the label order of the 19-row repeated-gap board, keep the pairs
   that lie inside a 15-row window, place them at columns 8j+1 with the gap 1,1,1,15,1,1,1,
   and check the resulting 15-row board. A rule common to both heights that is compatible
   with restriction would make this board valid.
"""
import json
import numpy as np
from boards import load_all, load_extra, HERE
from rectlib import check_board
from structure import quick_counts

bd = {n: (h, c) for n, h, c in load_all() + load_extra()}
rng = np.random.default_rng(7)


def order(cols):
    return [tuple(c) for c in cols if len(c) == 2]


def spearman(x, y):
    rx = np.argsort(np.argsort(x)); ry = np.argsort(np.argsort(y))
    return float(np.corrcoef(rx, ry)[0, 1])


out = {'rank_correlation': [], 'restriction': []}
pairs = [('h15_w441_mask8', 'h19_w713_binary'), ('h15_w441_mask8', 'h15_w441_mask10'),
         ('h15_w441_mask8', 'h15_w441_mask42'), ('h15_w441_binary', 'h15_w441_mask8'),
         ('h15_w441_oddsea', 'h15_w441_mask8'), ('h11_w169', 'h15_w441_mask8'),
         ('h11_w169', 'h11_cegar_h11_s4_hyb_t3_111'), ('h11_w169', 'h11_cegar_h11_mod4_j2_t4'),
         ('h7_w21_c', 'h11_w169'), ('h9_w77', 'h11_w169')]
for a, b in pairs:
    ha, ca = bd[a]; hb, cb = bd[b]
    oa = order(ca); ob = {p: i for i, p in enumerate(order(cb))}
    for shift in sorted({0, (hb - ha) // 2 * 1 if (hb - ha) % 4 == 0 else 0, hb - ha}):
        if shift % 2:
            continue
        xs = []; ys = []
        for i, (r, s) in enumerate(oa):
            p = (r + shift, s + shift)
            if p in ob:
                xs.append(i); ys.append(ob[p])
        rho = spearman(np.array(xs), np.array(ys))
        null = [abs(spearman(rng.permutation(len(xs)), np.array(ys))) for _ in range(500)]
        out['rank_correlation'].append({'lower': a, 'upper': b, 'row_shift': shift, 'common_pairs': len(xs),
                                        'spearman': round(rho, 3),
                                        'null_abs_95_percentile': round(float(np.percentile(null, 95)), 3)})
        print(out['rank_correlation'][-1], flush=True)

h19 = order(bd['h19_w713_binary'][1])
for shift in (0, 2, 4):
    sub = [(r - shift, s - shift) for r, s in h19 if 1 <= r - shift <= 15 and 1 <= s - shift <= 15]
    cols = []
    for j, p in enumerate(sub):
        cols.append(sorted(p))
        if j < len(sub) - 1:
            cols.extend([[1], [1], [1], [15], [1], [1], [1]])
    chk = check_board(15, cols)
    fatal, ver, _ = quick_counts(15, cols)
    rec = {'rows_of_19_used': [1 + shift, 15 + shift], 'labels': len(sub), 'valid': chk['valid'],
           'clashing_presentations': chk['rectangles_with_two_or_more_black_corners'] - chk['hidden_rectangles']
                                     - chk['distinct_presentations_among_them'],
           'fatal_triangles': fatal, 'vertical_rival_pairs': ver}
    out['restriction'].append(rec); print(rec, flush=True)
(HERE / 'cross_board.json').write_text(json.dumps(out, indent=1))
