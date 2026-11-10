"""Structure extraction for the stored equality boards (heights 7, 11, 15, 19, with 9 as a control).

For every board: label order and gaps, arithmetic fits of the order, filler rows,
three-black tilted right angles, tilted shapes with two or more black corners,
and the vertical-rival (Pythagorean) check. Results go to structure.json.
"""
import json, sys
from collections import Counter
from math import gcd, isqrt
import numpy as np
from boards import load_all, load_extra, HERE

rng = np.random.default_rng(20261109)


def tilted_shapes(h):
    """Each tilted rectangle shape once: corners P, P+u, P+v, P+u+v with u = s(p,q), v = t(-q,p)."""
    out = []
    for p in range(1, h):
        for q in range(1, h):
            if gcd(p, q) != 1:
                continue
            for s in range(1, h):
                if s * q > h - 1:
                    break
                for t in range(1, h):
                    if s * q + t * p > h - 1:
                        break
                    u = (s * p, s * q); v = (-t * q, t * p)
                    pts = [(0, 0), u, (u[0] + v[0], u[1] + v[1]), v]      # cyclic order
                    mc = min(c for c, _ in pts)
                    key = tuple(sorted([(s * p, s * q), (t * q, t * p)]))
                    out.append(([(c - mc, r) for c, r in pts], key))
    return out


def analyse(name, h, cols):
    m = len(cols)
    q = h * h // 4
    res = {'name': name, 'height': h, 'width': m}
    B = np.zeros((m, h), dtype=np.int8)
    for x, c in enumerate(cols):
        for r in c:
            B[x, r - 1] = 1
    is_label_col = np.array([len(c) == 2 for c in cols])
    labels = [(x + 1, *sorted(c, key=lambda r: (r % 2 == 0, r))) for x, c in enumerate(cols) if len(c) == 2]
    parity_graph = all(a % 2 == 1 and b % 2 == 0 for _, a, b in labels) and \
        len({(a, b) for _, a, b in labels}) == q == len(labels)
    res['row_partition'] = 'odd rows / even rows' if parity_graph else 'other'
    res['all_odd_even_pairs_once'] = parity_graph
    lc = np.array([x for x, _, _ in labels]); la = np.array([a for _, a, _ in labels]); lb = np.array([b for _, _, b in labels])
    first, last = int(lc[0]), int(lc[-1])
    res['label_columns'] = lc.tolist()
    res['label_order'] = [[int(a), int(b)] for a, b in zip(la, lb)]
    gaps = np.diff(lc)
    res['gap_histogram'] = {int(k): int(v) for k, v in sorted(Counter(gaps.tolist()).items())}
    res['core'] = [first, last, last - first + 1]
    res['single_residue_moduli'] = [g for g in range(2, 17) if len(set((lc % g).tolist())) == 1]

    # ---- (a) arithmetic fits of the order ----
    n = len(lc); slot = np.arange(n)
    X = np.stack([la, lb, np.ones(n)], axis=1).astype(float)
    fits = {}
    for nm, y in (('column', lc.astype(float)), ('slot', slot.astype(float))):
        coef, *_ = np.linalg.lstsq(X, y, rcond=None)
        ss = ((y - X @ coef) ** 2).sum(); tot = ((y - y.mean()) ** 2).sum()
        fits[nm] = {'alpha_odd_row': round(float(coef[0]), 3), 'beta_even_row': round(float(coef[1]), 3),
                    'gamma': round(float(coef[2]), 3), 'R2': round(float(1 - ss / tot), 4)}
    res['linear_fit'] = fits
    # shuffled-order reference for R2
    r2 = []
    for _ in range(300):
        y = rng.permutation(n).astype(float)
        coef, *_ = np.linalg.lstsq(X, y, rcond=None)
        r2.append(1 - ((y - X @ coef) ** 2).sum() / ((y - y.mean()) ** 2).sum())
    res['linear_fit']['slot_R2_shuffled_mean_max'] = [round(float(np.mean(r2)), 4), round(float(np.max(r2)), 4)]

    ia = (la + 1) // 2; ib = lb // 2          # rank of each row inside its class

    def best_mod(y, N):
        al, be, ga = np.meshgrid(np.arange(N), np.arange(N), np.arange(N), indexing='ij')
        ok = (al.ravel() != 0) | (be.ravel() != 0)
        al, be, ga = al.ravel()[ok], be.ravel()[ok], ga.ravel()[ok]
        pred = (al[:, None] * ia[None, :] + be[:, None] * ib[None, :] + ga[:, None]) % N
        hit = (pred == (y % N)[None, :]).sum(axis=1)
        i = int(hit.argmax())
        return int(hit[i]), (int(al[i]), int(be[i]), int(ga[i]))

    mod = {}
    for N in range(2, 13):
        hs, par = best_mod(slot, N)
        hc, parc = best_mod(lc, N)
        sh = [best_mod(rng.permutation(n), N)[0] for _ in range(40)]
        mod[N] = {'slot_best_fraction': round(hs / n, 3), 'slot_best_alpha_beta_gamma': par,
                  'column_best_fraction': round(hc / n, 3),
                  'shuffled_mean': round(float(np.mean(sh)) / n, 3), 'shuffled_max': round(float(np.max(sh)) / n, 3)}
    res['modular_fit_slot_eq_alpha_i_plus_beta_j_plus_gamma'] = mod

    def determined(y, K, M):
        tab = Counter(zip((la % M).tolist(), (lb % M).tolist(), (y % K).tolist()))
        cells = Counter()
        best = Counter()
        for (a, b, v), c in tab.items():
            best[a, b] = max(best[a, b], c)
        return sum(best.values()) / n

    res['slot_class_explained_by_row_residues'] = {
        f'slot mod {K} from rows mod {M}': [round(determined(slot, K, M), 3),
                                            round(float(np.mean([determined(rng.permutation(n), K, M) for _ in range(100)])), 3)]
        for K in (2, 4) for M in (2, 4, 8)}
    share = float(np.mean([(la[i] == la[i + 1]) or (lb[i] == lb[i + 1]) for i in range(n - 1)]))
    shs = []
    for _ in range(300):
        pm = rng.permutation(n)
        shs.append(np.mean([(la[pm[i]] == la[pm[i + 1]]) or (lb[pm[i]] == lb[pm[i + 1]]) for i in range(n - 1)]))
    res['consecutive_labels_sharing_a_row'] = [round(share, 3), round(float(np.mean(shs)), 3)]
    res['adjacent_row_pairs_consecutive_staircase_steps'] = int(sum(
        abs(la[i] - lb[i]) == 1 and abs(la[i + 1] - lb[i + 1]) == 1 and
        len({la[i], lb[i]} & {la[i + 1], lb[i + 1]}) == 1 for i in range(n - 1)))

    # ---- (b) fillers ----
    fill = [(x + 1, c[0]) for x, c in enumerate(cols) if len(c) == 1]
    core_fill = [r for x, r in fill if first <= x <= last]
    hist = Counter(r for _, r in fill); hc_ = Counter(core_fill)
    res['filler_histogram_whole_board'] = {int(k): int(v) for k, v in sorted(hist.items())}
    res['filler_histogram_core'] = {int(k): int(v) for k, v in sorted(hc_.items())}
    nc = max(1, len(core_fill))
    res['core_filler_fraction_row_1'] = round(hc_[1] / nc, 3)
    res['core_filler_fraction_row_h'] = round(hc_[h] / nc, 3)
    res['core_filler_fraction_interior'] = round(1 - (hc_[1] + hc_[h]) / nc, 3)
    res['core_filler_fraction_even_rows'] = round(sum(v for k, v in hc_.items() if k % 2 == 0) / nc, 3)
    wordv = [0 if len(c) == 2 else c[0] for c in cols[first - 1:last]]
    gw = Counter()
    for i in range(n - 1):
        gw[','.join(str(cols[x][0]) for x in range(lc[i], lc[i + 1] - 1))] += 1
    res['gap_words'] = [[k, v] for k, v in gw.most_common(8)]
    res['distinct_gap_words'] = len(gw)
    per = []
    wv = np.array(wordv)
    for p in range(1, min(65, len(wv) // 2)):
        per.append((round(float((wv[:-p] == wv[p:]).mean()), 3), p))
    per.sort(key=lambda t: (-t[0], t[1]))      # best match first, shortest period first
    res['core_word_best_periods_fraction_period'] = per[:3]

    # ---- (c), (d): tilted rectangles by shape ----
    Lm = B * is_label_col[:, None].astype(np.int8)
    cls = (np.arange(1, h + 1) % 2)                      # 1 for odd rows
    tri = Counter(); tri_rowdiff = Counter()
    per_label = np.zeros(m, dtype=np.int64)
    shape_max = {}; shape_full = {}
    two = Counter()
    placements = 0; weak_placements = 0
    for pts, key in tilted_shapes(h):
        sw = max(c for c, _ in pts); sh_ = max(r for _, r in pts)
        if sw > m - 1:
            continue
        shape_full[key] = (sh_ == h - 1)
        shape_max.setdefault(key, 0)
        V = [B[c:m - sw + c, r:h - sh_ + r] for c, r in pts]
        cnt = V[0] + V[1] + V[2] + V[3]
        mx = int(cnt.max()) if cnt.size else 0
        placements += cnt.size; weak_placements += int((cnt >= 2).sum())
        shape_max[key] = max(shape_max[key], mx)
        if mx < 2:
            continue
        LV = [Lm[c:m - sw + c, r:h - sh_ + r] for c, r in pts]
        xs, ys = np.nonzero(cnt == 2)
        if len(xs):
            bl = np.stack([V[k][xs, ys] for k in range(4)], axis=1)
            lb_ = np.stack([LV[k][xs, ys] for k in range(4)], axis=1)
            nl = (lb_ * bl).sum(axis=1)
            opp = ((bl[:, 0] & bl[:, 2]) | (bl[:, 1] & bl[:, 3])).astype(bool)
            u_, c_ = np.unique(np.stack([nl, opp.astype(np.int64)], axis=1), axis=0, return_counts=True)
            for (a_, o_), n_ in zip(u_.tolist(), c_.tolist()):
                two[('filler-filler', 'filler-label', 'label-label')[a_], 'diagonal' if o_ else 'side',
                    'full height' if sh_ == h - 1 else 'shorter'] += n_
        xs, ys = np.nonzero(cnt == 3)
        if len(xs):
            bl = np.stack([V[k][xs, ys] for k in range(4)], axis=1)
            wk = bl.argmin(axis=1)                         # index of the white corner
            pc = np.array([c for c, _ in pts]); pr = np.array([r for _, r in pts])
            sc = xs + pc[wk]; sr = ys + pr[wk]             # completion cell (0-based)
            lbl = np.stack([LV[k][xs, ys] for k in range(4)], axis=1)
            nl = lbl.sum(axis=1)
            comp_label = is_label_col[sc]
            # rows of the black cell(s) in the completion column
            for i in range(len(xs)):
                rows = cols[sc[i]]
                same = all((r % 2) == ((sr[i] + 1) % 2) for r in rows)
                tri[int(nl[i]), 'label column' if comp_label[i] else 'filler column',
                    'same class' if same else 'opposite class present'] += 1
                if not comp_label[i]:
                    tri_rowdiff[abs(rows[0] - (sr[i] + 1))] += 1
                seen = set()
                for k in range(4):
                    if k != wk[i] and lbl[i, k]:
                        seen.add(int(xs[i] + pc[k]))
                for c_ in seen:
                    per_label[c_] += 1
    res['triangles_total'] = int(sum(tri.values()))
    res['triangles_by_labelcells_completioncolumn_class'] = [[*k, v] for k, v in sorted(tri.items())]
    res['triangles_by_number_of_label_cells'] = {str(k): int(sum(v for kk, v in tri.items() if kk[0] == k)) for k in range(4)}
    res['triangle_completion_row_distance_to_filler'] = {int(k): int(v) for k, v in sorted(tri_rowdiff.items())}
    pl = per_label[is_label_col]
    res['triangles_per_label_mean_max_min'] = [round(float(pl.mean()), 2), int(pl.max()), int(pl.min())]
    res['triangles_per_column'] = round(res['triangles_total'] / m, 3)
    tot = len(shape_max)
    res['tilted_shape_classes_fitting'] = tot
    res['shape_classes_never_two_black'] = sum(1 for v in shape_max.values() if v < 2)
    res['shape_classes_neutralized_fraction'] = round(res['shape_classes_never_two_black'] / tot, 3)
    res['shape_classes_with_three_black'] = sum(1 for v in shape_max.values() if v >= 3)
    fh = [k for k in shape_max if shape_full[k]]; nf = [k for k in shape_max if not shape_full[k]]
    res['full_height_classes_total_neutralized'] = [len(fh), sum(1 for k in fh if shape_max[k] < 2)]
    res['shorter_classes_total_neutralized'] = [len(nf), sum(1 for k in nf if shape_max[k] < 2)]
    res['tilted_placements'] = placements
    res['tilted_placements_with_two_or_more_black'] = weak_placements
    res['fraction_with_two_or_more_black'] = round(weak_placements / placements, 5)
    res['two_black_rectangles_by_type'] = [[*k, v] for k, v in sorted(two.items())]

    # ---- (e) vertical rivals ----
    black = [(x, r) for x, c in enumerate(cols) for r in c]
    byc = {}
    for x, r in black:
        byc.setdefault(x, []).append(r)
    ver = Counter(); viol = 0; opp_pairs = 0; opp_pairs_dx4 = 0
    lab_gap4 = Counter()
    for x, r in black:
        for dx in range(1, h):
            if x + dx >= m:
                break
            for r2 in byc[x + dx]:
                dy = r2 - r
                if dy % 2 == 0:
                    continue
                opp_pairs += 1
                if dx % 4 == 0:
                    opp_pairs_dx4 += 1
                L2 = dx * dx + dy * dy; L = isqrt(L2)
                if L * L != L2 or L > h - 1:
                    continue
                mid2 = r + r2                                  # twice the midpoint row
                fits = (mid2 - L) >= 2 and (mid2 + L) <= 2 * h
                kind = ('label' if is_label_col[x] else 'filler') + '-' + ('label' if is_label_col[x + dx] else 'filler')
                kind = 'filler-label' if kind == 'label-filler' else kind
                ver[kind, f'({dx},{abs(dy)},{L})', 'fits: violation' if fits else 'blocked by the boundary'] += 1
                viol += fits
    res['vertical_rival_violations'] = int(viol)
    res['pythagorean_opposite_class_pairs'] = [[*k, v] for k, v in sorted(ver.items())]
    res['opposite_class_pairs_within_h_columns'] = opp_pairs
    res['of_which_column_difference_divisible_by_4'] = opp_pairs_dx4
    fc = Counter()
    for x, c in enumerate(cols):
        if len(c) == 1:
            near = lc[np.abs(lc - (x + 1)).argmin()]
            fc[(x + 1 - int(near)) % 4, 'odd' if c[0] % 2 else 'even'] += 1
    res['filler_column_offset_mod4_from_nearest_label_by_row_class'] = [[*k, v] for k, v in sorted(fc.items())]
    # ---- reference: the same columns and fillers with the label order shuffled ----
    lab_idx = [x for x, c in enumerate(cols) if len(c) == 2]
    fat = []; ver_s = []; weak_s = []
    for _ in range(SHUFFLES):
        pm = rng.permutation(len(lab_idx))
        sc_ = [list(c) for c in cols]
        for i, j in zip(lab_idx, pm):
            sc_[i] = list(cols[lab_idx[j]])
        f_, v_, w_ = quick_counts(h, sc_)
        fat.append(f_); ver_s.append(v_); weak_s.append(w_)
    f0, v0, w0 = quick_counts(h, cols)
    res['fatal_triangles_actual'] = f0
    res['shuffled_order_fatal_triangles_mean_min'] = [round(float(np.mean(fat)), 1), int(np.min(fat))]
    res['shuffled_order_fatal_triangles_per_label'] = round(float(np.mean(fat)) / len(lab_idx), 2)
    res['shuffled_order_vertical_rival_pairs_mean_min'] = [round(float(np.mean(ver_s)), 1), int(np.min(ver_s))]
    res['shuffled_order_fraction_without_vertical_rival'] = round(float(np.mean(np.array(ver_s) == 0)), 3)
    # random filler rows (same columns, same labels): density reference
    rc = [list(c) if len(c) == 2 else [int(rng.integers(1, h + 1))] for c in cols]
    res['random_filler_rows_fraction_with_two_or_more_black'] = round(quick_counts(h, rc)[2] / placements, 5)
    return res


SHUFFLES = 30
_SH = {}


def quick_counts(h, cols):
    """(fatal three-black tilted rectangles, vertical-rival pairs, tilted placements with >= 2 black).
    A three-black tilted rectangle is fatal when the column of its white corner holds a black cell
    in the row class opposite to the white corner (single axis rival)."""
    m = len(cols)
    B = np.zeros((m, h), dtype=np.int8)
    for x, c in enumerate(cols):
        for r in c:
            B[x, r - 1] = 1
    odd = B[:, 0::2].sum(axis=1) > 0      # rows 1,3,5,... black in the column
    even = B[:, 1::2].sum(axis=1) > 0
    if h not in _SH:
        _SH[h] = tilted_shapes(h)
    fatal = 0; weak = 0
    for pts, key in _SH[h]:
        sw = max(c for c, _ in pts); sh_ = max(r for _, r in pts)
        if sw > m - 1:
            continue
        V = [B[c:m - sw + c, r:h - sh_ + r] for c, r in pts]
        cnt = V[0] + V[1] + V[2] + V[3]
        weak += int((cnt >= 2).sum())
        xs, ys = np.nonzero(cnt == 3)
        if len(xs):
            bl = np.stack([V[k][xs, ys] for k in range(4)], axis=1)
            wk = bl.argmin(axis=1)
            pc = np.array([c for c, _ in pts]); pr = np.array([r for _, r in pts])
            sc = xs + pc[wk]; sr = ys + pr[wk]
            white_odd = (sr % 2 == 0)                 # 0-based row index even means odd row number
            fatal += int(np.where(white_odd, even[sc], odd[sc]).sum())
    byc = [c for c in cols]
    ver = 0
    for x in range(m):
        for r in byc[x]:
            for dx in range(4, h, 4):
                if x + dx >= m:
                    break
                for r2 in byc[x + dx]:
                    dy = r2 - r
                    if dy % 2 == 0:
                        continue
                    L2 = dx * dx + dy * dy; L = isqrt(L2)
                    if L * L == L2 and L <= h - 1 and (r + r2 - L) >= 2 and (r + r2 + L) <= 2 * h:
                        ver += 1
    return fatal, ver, weak


def klein_orbit(boards):
    """Are the four 7 x 21 boards one orbit under the two reflections?"""
    def key(c):
        return tuple(tuple(x) for x in c)
    b0 = boards[0][2]
    imgs = {key(b0), key(b0[::-1]), key([sorted(8 - r for r in c) for c in b0]),
            key([sorted(8 - r for r in c) for c in b0[::-1]])}
    return imgs == {key(b[2]) for b in boards}


if __name__ == '__main__':
    main_boards = load_all()
    extra = [b for b in load_extra()]
    out = {'seven_row_boards_form_one_reflection_orbit': klein_orbit(main_boards[:4]), 'boards': []}
    for name, h, cols in main_boards + extra:
        r = analyse(name, h, cols)
        out['boards'].append(r)
        print(name, 'triangles', r['triangles_total'], 'vertical violations', r['vertical_rival_violations'], flush=True)
        (HERE / 'structure.json').write_text(json.dumps(out, indent=1, default=int))
