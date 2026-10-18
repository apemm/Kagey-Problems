"""Closed form of the three-row correction term E_m, rechecked without sympy.

Inputs: the forbidden-window table extracted from the definitional optima by
three_row_definition_check.py (compared here with the archive's table).  The
class counts N_AC, N_AB, N_BC, N_X of candidate words avoiding the windows
are computed by a small dynamic programme, giving a_3(m) = N_AC + N_AB +
N_BC + N_X and E_m = 2 N_AB + N_X (which equals a_3(m) - 4(m-1)(3m+2)3^(m-5)
for m >= 4).  The minimal linear recurrence of E_m is found by
Berlekamp-Massey over the rationals from more than twice as many terms as
the dimension of the dynamic programme, which certifies it; the closed form
is evaluated exactly in Q(sqrt 3) and Q(sqrt -2) with fractions and compared
with E_m term by term; and E_m > 0 for all m >= 4 is derived from explicit
rational bounds.  Everything is exact; no floating point is used.
"""
import json
import os
import sys
import time
from collections import defaultdict
from fractions import Fraction as Fr
from pathlib import Path

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(os.path.dirname(HERE), 'data')
TABLE_FILE = os.path.join(DATA, 'three_row_definition_check.json')
OUT = os.path.join(DATA, 'three_row_formula_check.json')
ARCHIVE = Path(__file__).resolve().parent.parent / 'data' / 'three_row_reference'
ARCHIVE_TABLE = ARCHIVE / 'three_row_windows.json'
ARCHIVE_COUNTS = ARCHIVE / 'three_row_transfer_counts.json'
ARCHIVE_RECURRENCE = ARCHIVE / 'three_row_recurrence.json'
M_MAX = 240

STATED_A3 = {3: 53, 4: 224, 5: 892, 6: 3420, 7: 12704, 8: 45864, 9: 161992, 10: 562912,
             11: 1930312, 12: 6545496, 13: 21988784, 14: 73296272, 15: 242715784}
STATED_E = {4: 168, 5: 620, 6: 2220, 7: 7736, 8: 26208, 9: 86824, 10: 282976, 11: 909712,
            12: 2888832}
STATED_DENOMINATOR = [1, -6, 12, -20, 36, 0, 0, 0, -144, -160, -192, -192, -64]


def class_alphabet(K):
    return ['a', 'b', 'c'] + (['X'] if K == 'X' else list(K))


def class_counts(K, forbidden, m_max):
    """N_K(m) for 0 <= m <= m_max and the number of reachable states."""
    letters = class_alphabet(K)
    need = frozenset('X') if K == 'X' else frozenset(K)
    states = {('', '', frozenset()): 1}
    counts = [0]
    reachable = set(states)
    for _ in range(m_max):
        new = defaultdict(int)
        for (p2, p1, used), cnt in states.items():
            for L in letters:
                if L in need and L in used:
                    continue
                if p2 and (p2 + p1 + L) in forbidden:
                    continue
                u = used | {L} if L in need else used
                new[(p1, L, u)] += cnt
        states = new
        reachable |= set(states)
        counts.append(sum(c for (p2, p1, used), c in states.items() if used == need))
    return counts, len(reachable)


def reflect_word(w):
    return w.translate(str.maketrans('acAC', 'caCA'))


def berlekamp_massey(seq):
    """Minimal connection polynomial c (ascending, c[0] = 1) with
    sum_i c[i] s[n-i] = 0 for every n >= len(c) - 1."""
    C = [Fr(1)]
    B = [Fr(1)]
    L = 0
    shift = 1
    b = Fr(1)
    for n, s in enumerate(seq):
        d = s + sum(C[i] * seq[n - i] for i in range(1, L + 1))
        if d == 0:
            shift += 1
            continue
        T = C[:]
        coef = d / b
        need = len(B) + shift
        if need > len(C):
            C = C + [Fr(0)] * (need - len(C))
        for i, bi in enumerate(B):
            C[i + shift] -= coef * bi
        if 2 * L <= n:
            L = n + 1 - L
            B = T
            b = d
            shift = 1
        else:
            shift += 1
    C = C[:L + 1]
    for n in range(L, len(seq)):
        assert sum(C[i] * seq[n - i] for i in range(L + 1)) == 0
    return C


def poly_mul(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out


def poly_pow(p, n):
    out = [1]
    for _ in range(n):
        out = poly_mul(out, p)
    return out


class Q3:
    """a + b sqrt 3 with rational a, b."""
    __slots__ = ('a', 'b')

    def __init__(self, a, b=0):
        self.a = Fr(a)
        self.b = Fr(b)

    def __add__(self, o):
        return Q3(self.a + o.a, self.b + o.b)

    def __mul__(self, o):
        return Q3(self.a * o.a + 3 * self.b * o.b, self.a * o.b + self.b * o.a)

    def __pow__(self, n):
        r = Q3(1)
        for _ in range(n):
            r = r * self
        return r


class Qm2:
    """a + b i sqrt 2 with rational a, b."""
    __slots__ = ('a', 'b')

    def __init__(self, a, b=0):
        self.a = Fr(a)
        self.b = Fr(b)

    def __add__(self, o):
        return Qm2(self.a + o.a, self.b + o.b)

    def __mul__(self, o):
        return Qm2(self.a * o.a - 2 * self.b * o.b, self.a * o.b + self.b * o.a)

    def __pow__(self, n):
        r = Qm2(1)
        for _ in range(n):
            r = r * self
        return r


def closed_form(m):
    """E_m from the stated closed form, exactly; returns (value, sqrt3 part, T_m, T_m via i sqrt2)."""
    rho = Q3(1, 1)
    sigma = Q3(1, -1)
    p_plus = Q3(Fr(19 * m * m + 61 * m + 104, 432), Fr(11 * m * m + 41 * m + 28, 432))
    p_minus = Q3(Fr(19 * m * m + 61 * m + 104, 432), Fr(-(11 * m * m + 41 * m + 28), 432))
    main = p_plus * rho ** m + p_minus * sigma ** m
    if m % 2 == 0:
        T = Fr((-1) ** (m // 2) * 2 ** (m // 2) * (2 * m * m + 41 * m - 104), 216)
    else:
        T = Fr((-1) ** ((m - 1) // 2) * 2 ** ((m - 1) // 2) * (7 * m * m - 32 * m - 175), 432)
    q = Qm2(Fr(m * m, 216) + Fr(41 * m, 432) - Fr(13, 54),
            Fr(-7 * m * m, 1728) + Fr(m, 54) + Fr(175, 1728))
    qbar = Qm2(q.a, -q.b)
    T2 = q * Qm2(0, 1) ** m + qbar * Qm2(0, -1) ** m
    assert T2.b == 0
    return main.a + T, main.b, T, T2.a


def positivity_certificate():
    """Exact rational constants proving E_m > 0 for every m >= 4 from the closed form.

    For m >= 4: p_+(m) >= (19/432) m^2 (every coefficient of p_+ is positive);
    rho = 1 + sqrt 3 >= r; |sigma| < 1; |p_-(m)| <= c1 m^2; |T_m| <= c2 m^2 2^(m/2).
    Hence E_m >= m^2 2^(m/2) [ (19/432) (rho / sqrt 2)^m - c1 - c2 ] and it suffices
    that t^4 > (c1 + c2) 432/19 with t <= rho / sqrt 2, t > 1.
    """
    s_lo, s_hi = Fr(173, 100), Fr(17321, 10000)       # sqrt 3 bounds
    assert s_lo ** 2 < 3 < s_hi ** 2
    r2_hi = Fr(14143, 10000)                           # sqrt 2 upper bound
    assert r2_hi ** 2 > 2
    r = 1 + s_lo                                       # rho lower bound
    c1 = ((19 + 11 * s_hi) + (61 + 41 * s_hi) / 4 + (104 + 28 * s_hi) / 16) / 432
    c2 = max((2 + Fr(41, 4) + Fr(104, 16)) / 216, (7 + 8 + Fr(175, 16)) / 432)
    t = r / r2_hi
    threshold = (c1 + c2) * 432 / 19
    ok = t > 1 and t ** 4 > threshold
    return {'sqrt3_bounds': [str(s_lo), str(s_hi)], 'sqrt2_upper': str(r2_hi),
            'rho_lower': str(r), 'c1': str(c1), 'c2': str(c2), 't': str(t),
            't_to_4': str(t ** 4), 'threshold': str(threshold), 'holds': ok}


def main():
    t0 = time.time()
    with open(TABLE_FILE) as f:
        defn = json.load(f)
    table = {K: set(v) for K, v in defn['window_table'].items()}
    with open(ARCHIVE_TABLE) as f:
        arch = json.load(f)['local']
    archive_table = {K: set(arch[K]['bad']) for K in arch}
    table_agrees = {K: table[K] == archive_table[K] for K in archive_table}
    table_agrees['BC_is_reflected_AB'] = table['BC'] == {reflect_word(w) for w in table['AB']}
    result = {'date': '2026-10-17', 'python': sys.version.split()[0], 'method': 'fractions only, no sympy',
              'window_table_source': 'three_row_definition_check.json (tested through width %s)'
              % defn.get('window_table_tested_through'),
              'window_table_agrees_with_archive': table_agrees}

    counts = {}
    dims = {}
    for K in ('AC', 'AB', 'BC', 'X'):
        counts[K], dims[K] = class_counts(K, table[K], M_MAX)
    result['dp_state_dimensions'] = dims
    assert counts['AB'] == counts['BC']
    a3 = [sum(counts[K][m] for K in counts) for m in range(M_MAX + 1)]
    E = [2 * counts['AB'][m] + counts['X'][m] for m in range(M_MAX + 1)]
    result['a3_0_to_15'] = a3[:16]
    result['a3_matches_stated_3_to_15'] = all(a3[m] == v for m, v in STATED_A3.items())
    with open(ARCHIVE_COUNTS) as f:
        archive_counts = json.load(f)['counts_m_0_through_40']
    result['a3_matches_archive_transfer_0_to_40'] = a3[:41] == archive_counts
    result['E_2_to_12'] = E[2:13]
    result['E_matches_stated_4_to_12'] = all(E[m] == v for m, v in STATED_E.items())
    result['formal_E_2_E_3'] = [E[2], E[3]]
    result['AC_count_equals_4(m-1)(3m+2)3^(m-5)_for_4_to_M'] = all(
        Fr(counts['AC'][m]) == Fr(4 * (m - 1) * (3 * m + 2) * 3 ** m, 3 ** 5) for m in range(4, M_MAX + 1))
    result['E_equals_a3_minus_AC_term_4_to_M'] = all(
        Fr(E[m]) == a3[m] - Fr(4 * (m - 1) * (3 * m + 2) * 3 ** m, 3 ** 5) for m in range(4, M_MAX + 1))

    # minimal recurrence of E_m (from m = 2) and of a_3(m) (from m = 3), certified by the state dimension
    need_terms = 2 * (dims['AB'] + dims['X']) + 20
    assert M_MAX - 1 >= need_terms
    cE = berlekamp_massey([Fr(x) for x in E[2:]])
    expected = poly_pow([1, -2, -2], 3)
    expected = poly_mul(expected, poly_pow([1, 0, 2], 3))
    result['stated_denominator_equals_(1-2z-2z^2)^3(1+2z^2)^3'] = expected == STATED_DENOMINATOR
    result['E_minimal_recurrence'] = [str(c) for c in cE]
    result['E_minimal_recurrence_order'] = len(cE) - 1
    result['E_recurrence_equals_stated_order_12'] = [int(c) for c in cE] == STATED_DENOMINATOR
    result['E_recurrence_terms_used'] = M_MAX - 1
    result['E_recurrence_certified_terms_needed'] = need_terms
    with open(ARCHIVE_RECURRENCE) as f:
        arch = json.load(f)
    arch_rec = arch['denominator_coefficients_ascending']
    first = arch['vector_identity_starts_at']
    result['a3_archive_denominator_order'] = len(arch_rec) - 1
    result['a3_archive_recurrence_first_index'] = first
    result['a3_archive_recurrence_holds_from_first_index_to_M'] = all(
        sum(arch_rec[i] * a3[m - i] for i in range(len(arch_rec))) == 0 for m in range(first, M_MAX + 1))
    result['a3_archive_recurrence_fails_just_before_first_index'] = (
        sum(arch_rec[i] * a3[first - 1 - i] for i in range(len(arch_rec))) != 0)
    cA3 = berlekamp_massey([Fr(x) for x in a3[3:]])
    cA4 = berlekamp_massey([Fr(x) for x in a3[4:]])
    result['a3_minimal_recurrence_order_from_m3_and_m4'] = [len(cA3) - 1, len(cA4) - 1]
    result['a3_recurrence_from_m4_equals_archive_(1-3z)^3(1-2z-2z^2)^3(1+2z^2)^3'] = [int(c) for c in cA4] == arch_rec

    # closed form evaluated exactly
    matches = []
    sqrt3_part_zero = True
    T_forms_agree = True
    F = {}
    for m in range(2, 101):
        val, s3, T, T2 = closed_form(m)
        F[m] = val
        matches.append(val == E[m])
        sqrt3_part_zero &= (s3 == 0)
        T_forms_agree &= (T == T2)
    result['closed_form_sqrt3_part_vanishes_2_to_100'] = sqrt3_part_zero
    result['T_parity_form_equals_i_sqrt2_form_2_to_100'] = T_forms_agree
    result['closed_form_equals_E_2_to_100'] = all(matches)
    result['closed_form_equals_E_2_to_13'] = all(matches[:12])
    order = len(cE) - 1
    result['closed_form_satisfies_E_recurrence_14_to_100'] = all(
        sum(cE[i] * F[m - i] for i in range(order + 1)) == 0 for m in range(2 + order, 101))
    result['identity_proof'] = (
        'E_m satisfies the certified minimal recurrence for every m >= 14; the closed form satisfies '
        'the same recurrence for every m because its roots are 1+sqrt3, 1-sqrt3, i sqrt2, -i sqrt2, each '
        'of multiplicity 3, and the coefficient polynomials have degree <= 2; the two sides agree at '
        'm = 2..13, hence for every m >= 2.')
    result['leading_coefficients_nonzero'] = {
        'p_plus_m2': '(19+11 sqrt3)/432 > 0', 'p_minus_m2': '(19-11 sqrt3)/432 != 0 since 19^2 = 361 != 363',
        'T_even_m2': '2/216', 'T_odd_m2': '7/432'}
    result['positivity'] = positivity_certificate()
    result['E_positive_4_to_M'] = all(E[m] > 0 for m in range(4, M_MAX + 1))
    result['seconds'] = round(time.time() - t0, 1)
    with open(OUT, 'w') as f:
        json.dump(result, f, indent=1)
    for k, v in result.items():
        print(k, ':', v)


if __name__ == '__main__':
    main()
