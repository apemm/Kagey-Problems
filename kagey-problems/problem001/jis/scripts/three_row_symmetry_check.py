"""Fixed counts and orbit counts of the three-row optima under the Klein group.

The optima of width m are the candidate words avoiding the forbidden windows
of their class (table from three_row_definition_check.py, tested there
against the definition through width 10).  Here the words fixed by the row
reflection, the column reversal and the half turn are counted in two ways:
a direct search that fills the word from both ends and checks every window
as soon as it is determined (widths 3..22), and a dynamic programme over the
left half with the crossing windows applied at the centre (widths 3..80),
which assumes only that the table is invariant under the symmetry (verified).
The counts are compared with the definitional counts of
three_row_definition_check.json (widths 3..10), with the stated formulas in
f_n, with the stated generating functions (power series over fractions),
and the orbit counts follow by Burnside with a_3(m) from the window
dynamic programme of three_row_formula_check.py.
"""
import json
import os
import sys
import time
from collections import defaultdict
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from three_row_formula_check import class_alphabet, class_counts  # noqa: E402

DATA = os.path.join(os.path.dirname(HERE), 'data')
TABLE_FILE = os.path.join(DATA, 'three_row_definition_check.json')
OUT = os.path.join(DATA, 'three_row_symmetry_check.json')
M_DFS = 22
M_DP = 80
STATED_O3 = {3: 15, 4: 58, 5: 227, 6: 864, 7: 3190, 8: 11502, 9: 40549, 10: 140863, 11: 482755,
             12: 1636860, 13: 5497794, 14: 18325769, 15: 60680951}
STATED_V = {3: 1, 4: 0, 5: 2, 6: 0, 7: 4, 8: 0, 9: 12, 10: 0, 11: 36, 12: 0, 13: 96, 14: 0, 15: 256}
STATED_W = {3: 5, 4: 8, 5: 14, 6: 36, 7: 52, 8: 144, 9: 192, 10: 540, 11: 672, 12: 1944, 13: 2296,
            14: 6804, 15: 7764}

SWAP = str.maketrans('acAC', 'caCA')


def sigma(g, letter):
    return letter.translate(SWAP) if g in ('half_turn', 'reflection') else letter


def need(K):
    return frozenset('X') if K == 'X' else frozenset(K)


def fixed_by_search(K, m, forbidden, g):
    """Words of class K and length m fixed by g, by filling from both ends."""
    letters = class_alphabet(K)
    req = need(K)
    w = [None] * m
    order = []
    for i in range((m + 1) // 2):
        order.append(i)
    count = 0

    def windows_ok(i):
        for s in range(max(0, i - 2), min(i, m - 3) + 1):
            t = w[s:s + 3]
            if None in t:
                continue
            if ''.join(t) in forbidden:
                return False
        return True

    def rec(idx, used):
        nonlocal count
        if idx == len(order):
            if used == req:
                count += 1
            return
        i = order[idx]
        j = m - 1 - i
        for L in letters:
            if g == 'reflection':
                if sigma(g, L) != L:
                    continue
                partner = L if j != i else None
            else:
                partner = sigma(g, L) if j != i else None
                if j == i and sigma(g, L) != L:
                    continue
                if partner and partner not in letters:
                    continue
            new_used = used
            for x in ([L] + ([partner] if partner else [])):
                if x in req:
                    if x in new_used:
                        new_used = None
                        break
                    new_used = new_used | {x}
            if new_used is None:
                continue
            w[i] = L
            if partner:
                w[j] = partner
            if windows_ok(i) and (not partner or windows_ok(j)):
                rec(idx + 1, new_used)
            w[i] = None
            if partner:
                w[j] = None

    rec(0, frozenset())
    return count


def fixed_by_dp(K, m, forbidden, g):
    """Words of class K and length m fixed by g (reversal or half turn), by a
    dynamic programme over the left half; the right half is the mirror image."""
    if g == 'reflection':
        raise ValueError
    letters = class_alphabet(K)
    req = need(K)
    h = m // 2
    states = {('', '', ()): 1}
    for _ in range(h):
        new = defaultdict(int)
        for (p2, p1, used), cnt in states.items():
            for L in letters:
                if L in req and L in used:
                    continue
                if p2 and (p2 + p1 + L) in forbidden:
                    continue
                u = tuple(sorted(used + (L,))) if L in req else used
                new[(p1, L, u)] += cnt
        states = new
    total = 0
    for (p2, p1, used), cnt in states.items():
        mirror = tuple(sigma(g, x) for x in used)
        if m % 2 == 0:
            if p1 and (p2 + p1 + sigma(g, p1)) in forbidden and p2:
                continue
            multiset = used + mirror
            if len(multiset) == len(set(multiset)) and set(multiset) == req:
                total += cnt
        else:
            for c in letters:
                if sigma(g, c) != c:
                    continue
                if p2 and (p2 + p1 + c) in forbidden:
                    continue
                if p1 and (p1 + c + sigma(g, p1)) in forbidden:
                    continue
                multiset = used + mirror + ((c,) if c in req else ())
                if len(multiset) == len(set(multiset)) and set(multiset) == req:
                    total += cnt
    return total


def table_invariant(forbidden, g):
    image = {''.join(sigma(g, x) for x in reversed(t)) for t in forbidden}
    return image == set(forbidden)


def series(num, den, n):
    """Power series coefficients of num/den (ascending integer lists) to z^n."""
    out = []
    for k in range(n + 1):
        c = Fr(num[k] if k < len(num) else 0)
        for i in range(1, min(k, len(den) - 1) + 1):
            c -= den[i] * out[k - i]
        out.append(c / den[0])
    return out


def poly_mul(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out


def main():
    t0 = time.time()
    with open(TABLE_FILE) as f:
        defn = json.load(f)
    table = {K: set(v) for K, v in defn['window_table'].items()}
    result = {'date': '2026-10-17', 'python': sys.version.split()[0],
              'coordinates': 'one-based (column, row), (1,1) top left',
              'group': 'row reflection (a<->c, A<->C), column reversal, half turn'}
    classes = ('AC', 'AB', 'BC', 'X')
    result['table_invariant_under_half_turn'] = {K: table_invariant(table[K], 'half_turn') for K in ('AC', 'X')}
    result['table_invariant_under_reversal'] = {K: table_invariant(table[K], 'reversal') for K in classes}
    result['table_AB_maps_to_BC_under_half_turn'] = {''.join(sigma('half_turn', x) for x in reversed(t))
                                                      for t in table['AB']} == table['BC']

    # route 1: direct search from both ends, widths 3..22
    search = {}
    for m in range(3, M_DFS + 1):
        row = {}
        for g in ('reflection', 'reversal', 'half_turn'):
            row[g] = {K: fixed_by_search(K, m, table[K], g) for K in classes}
        search[m] = row
    # route 2: left-half dynamic programme, widths 3..80 (reflection: words over b, B, X)
    dp = {}
    for m in range(3, M_DP + 1):
        row = {}
        for g in ('reversal', 'half_turn'):
            row[g] = {K: fixed_by_dp(K, m, table[K], g) for K in classes}
        refl = 0
        for i in range(m):
            w = 'b' * i + 'X' + 'b' * (m - 1 - i)
            if not any(w[s:s + 3] in table['X'] for s in range(m - 2)):
                refl += 1
        row['reflection'] = {'X': refl, 'AC': 0, 'AB': 0, 'BC': 0}
        dp[m] = row
    result['search_equals_dp_3_to_%d' % M_DFS] = all(
        search[m][g] == dp[m][g] for m in search for g in search[m])
    r = {m: sum(dp[m]['reflection'].values()) for m in dp}
    v = {m: sum(dp[m]['reversal'].values()) for m in dp}
    w = {m: sum(dp[m]['half_turn'].values()) for m in dp}
    w_ac = {m: dp[m]['half_turn']['AC'] for m in dp}
    w_x = {m: dp[m]['half_turn']['X'] for m in dp}
    result['reflection_fixed_3_to_%d' % M_DP] = [r[m] for m in range(3, M_DP + 1)]
    result['reversal_fixed_3_to_30'] = [v[m] for m in range(3, 31)]
    result['half_turn_fixed_3_to_30'] = [w[m] for m in range(3, 31)]
    result['half_turn_fixed_AC_part_3_to_30'] = [w_ac[m] for m in range(3, 31)]
    result['half_turn_fixed_X_part_3_to_30'] = [w_x[m] for m in range(3, 31)]
    result['reflection_fixed_only_at_3'] = all(r[m] == (1 if m == 3 else 0) for m in r)
    result['reversal_fixed_zero_at_even_m'] = all(v[m] == 0 for m in v if m % 2 == 0)
    result['reversal_fixed_only_class_X'] = all(dp[m]['reversal'][K] == 0 for m in dp for K in ('AC', 'AB', 'BC'))
    result['half_turn_fixed_only_classes_AC_X'] = all(dp[m]['half_turn'][K] == 0 for m in dp for K in ('AB', 'BC'))

    # against the definitional counts (widths 3..10)
    defn_agree = True
    for m in range(3, 11):
        fx = defn['widths'][str(m)]['fixed']
        defn_agree &= (fx['reflection'] == r[m] and fx['reversal'] == v[m] and fx['half_turn'] == w[m])
    result['fixed_counts_equal_definitional_3_to_10'] = defn_agree
    result['v_matches_stated_3_to_15'] = all(v[m] == STATED_V[m] for m in STATED_V)
    result['w_matches_stated_3_to_15'] = all(w[m] == STATED_W[m] for m in STATED_W)

    # stated formulas
    f = [1, 3]
    for n in range(2, 60):
        f.append(2 * f[-1] + 2 * f[-2])
    v_formula_ok = v[3] == 1 and v[5] == 2
    x_formula_ok = w_x[3] == 3
    ac_formula_ok = w_ac[3] == 2
    for m in range(4, M_DP + 1):
        n = m // 2
        ac_formula_ok &= (w_ac[m] == 4 * n * 3 ** (n - 2))
        if m % 2 == 1:
            k = (m - 1) // 2
            if k >= 3:
                v_formula_ok &= (v[m] == 4 * f[(k + 1) // 2 - 2] * f[k // 2 - 1])
            if k >= 2:
                x_formula_ok &= (w_x[m] == 2 * f[(k + 1) // 2] * f[k // 2 - 1])
        else:
            x_formula_ok &= (w_x[m] == 0)
    result['v_formula_4f_f_holds_to_%d' % M_DP] = v_formula_ok
    result['x_formula_2f_f_holds_to_%d' % M_DP] = x_formula_ok
    result['AC_part_4n3^(n-2)_holds_to_%d' % M_DP] = ac_formula_ok
    result['w3_equals_5'] = w[3] == 5

    # stated generating functions (power series over fractions)
    den_vx = poly_mul([1, 0, -2, 0, -2], [1, 0, 0, 0, 2])
    v_series = series([0, 0, 0, 1], den_vx, M_DP)
    x_series = series([0, 0, 0, 3, 0, 0, 0, 4, 0, 4], den_vx, M_DP)
    ac_num = poly_mul([0, 0, 0, 2], poly_mul([1, -1], [1, 5, 3, -3]))
    ac_series = series(ac_num, poly_mul([1, 0, -3], [1, 0, -3]), M_DP)
    result['v_generating_function_matches_to_%d' % M_DP] = all(v_series[m] == v[m] for m in range(3, M_DP + 1))
    result['w_odd_part_generating_function_matches_to_%d' % M_DP] = all(
        x_series[m] == w_x[m] for m in range(3, M_DP + 1))
    result['w_AC_part_generating_function_matches_to_%d' % M_DP] = all(
        ac_series[m] == w_ac[m] for m in range(3, M_DP + 1))

    # Burnside with a_3 from the window dynamic programme
    counts = {K: class_counts(K, table[K], M_DP)[0] for K in classes}
    a3 = [sum(counts[K][m] for K in classes) for m in range(M_DP + 1)]
    o3 = {}
    divisible = True
    for m in range(3, M_DP + 1):
        tot = a3[m] + r[m] + v[m] + w[m]
        divisible &= (tot % 4 == 0)
        o3[m] = tot // 4
    result['burnside_sum_divisible_by_4_to_%d' % M_DP] = divisible
    result['o3_3_to_20'] = [o3[m] for m in range(3, 21)]
    result['o3_matches_stated_3_to_15'] = all(o3[m] == STATED_O3[m] for m in STATED_O3)
    result['o3_matches_definitional_orbits_3_to_10'] = all(
        o3[m] == defn['widths'][str(m)]['orbits'] for m in range(3, 11))
    result['fixed_words_m3_m4_from_definition'] = {
        m: defn['widths'][str(m)]['fixed_words'] for m in (3, 4)}
    result['seconds'] = round(time.time() - t0, 1)
    with open(OUT, 'w') as fh:
        json.dump(result, fh, indent=1)
    for k, val in result.items():
        print(k, ':', val)


if __name__ == '__main__':
    main()
