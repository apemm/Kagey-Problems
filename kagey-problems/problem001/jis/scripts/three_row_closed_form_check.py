"""Exact check of the three-row closed form without sympy (fractions only).

Independent second route for a_3(m) = 4(m-1)(3m+2)3^(m-5) + E_m:

1. a_3(m) for 0 <= m <= 100 is recomputed from the stored 350-state transfer matrix
   (integer matrix-vector iteration), from the stored rational function P/Q (power
   series division), and read from the stored coefficient list; the three must agree.
2. The twelve rational coefficients of the real-form ansatz
       E_m = 2 sum_k m^k (x_k P_m + 3 y_k Q_m)
             + [m even] 2 (-2)^(m/2) sum_k p_k m^k + [m odd] (-4)(-2)^((m-1)/2) sum_k q_k m^k,
   where (1+sqrt3)^m = P_m + Q_m sqrt3, are solved from E_4..E_15 by Gaussian elimination
   over the rationals, compared with the sympy derivation, and the closed form is then
   evaluated exactly for every 2 <= m <= 100 against the transfer counts.
3. a_3(m) for 3 <= m <= 7 is recounted from the definition: every (m+2)-subset of the
   3 x m grid is tested with verify_narrow.collision (all rectangles, tilted included),
   and no (m+3)-subset is valid.

Coordinates in the brute-force part follow verify_narrow: bit (row)*m + (column), zero
based internally; nothing coordinate-dependent is written out except counts.
Output: jis/data/three_row_closed_form_check.json.
"""
import json
import os
import sys
import time
from fractions import Fraction
from itertools import combinations
from pathlib import Path

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
DATA = os.path.join(os.path.dirname(HERE), 'data')
sys.path.insert(0, ROOT)
import verify_narrow  # noqa: E402

REFERENCE = Path(__file__).resolve().parent.parent / 'data' / 'three_row_reference'
TRANSFER = REFERENCE / 'three_row_transfer_matrix.json'
RECUR = REFERENCE / 'three_row_recurrence.json'
COUNTS = REFERENCE / 'three_row_classes.json'


def transfer_counts(n):
    with open(TRANSFER) as fh:
        t = json.load(fh)
    edges = [{int(k): v for k, v in d.items()} for d in t['edges']]
    acc = set(t['accepting_states'])
    vec = [0] * len(edges)
    for s in t['initial_states']:
        vec[s] += 1
    counts = []
    for _ in range(n + 1):
        counts.append(sum(vec[s] for s in acc))
        new = [0] * len(edges)
        for s, x in enumerate(vec):
            if x:
                for tgt, mult in edges[s].items():
                    new[tgt] += x * mult
        vec = new
    return counts, len(edges)


def series_quotient(num, den, n):
    """Coefficients 0..n of num(z)/den(z), den[0] = 1, integer arithmetic."""
    out = []
    for k in range(n + 1):
        v = num[k] if k < len(num) else 0
        for j in range(1, min(k, len(den) - 1) + 1):
            v -= den[j] * out[k - j]
        assert den[0] == 1
        out.append(v)
    return out


def solve_rational(A, b):
    n = len(A)
    M = [[Fraction(x) for x in row] + [Fraction(y)] for row, y in zip(A, b)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        piv = M[c][c]
        M[c] = [x / piv for x in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [x - f * y for x, y in zip(M[r], M[c])]
    return [M[r][n] for r in range(n)]


def pq(m):
    P, Q = 1, 0
    for _ in range(m):
        P, Q = P + 3 * Q, P + Q
    return P, Q


def ansatz_row(m):
    P, Q = pq(m)
    row = []
    for k in range(3):
        row.append(2 * m ** k * P)        # x_k
    for k in range(3):
        row.append(6 * m ** k * Q)        # y_k
    for k in range(3):
        row.append(2 * (-2) ** (m // 2) * m ** k if m % 2 == 0 else 0)      # p_k
    for k in range(3):
        row.append(-4 * (-2) ** ((m - 1) // 2) * m ** k if m % 2 == 1 else 0)  # q_k
    return row


def closed_form(coef, m):
    return sum(Fraction(c) * r for c, r in zip(coef, ansatz_row(m)))


def brute_counts(max_m, time_limit):
    results = {}
    start = time.time()
    for m in range(3, max_m + 1):
        rects = verify_narrow.rectangles(3, m)
        cells = 3 * m
        t = time.time()
        n_opt = sum(1 for S in combinations(range(cells), m + 2)
                    if verify_narrow.collision(rects, sum(1 << i for i in S)) is None)
        n_more = sum(1 for S in combinations(range(cells), m + 3)
                     if verify_narrow.collision(rects, sum(1 << i for i in S)) is None)
        results[m] = {'rectangles': len(rects), 'valid_size_m+2': n_opt, 'valid_size_m+3': n_more,
                      'seconds': round(time.time() - t, 2)}
        print('brute m=%d: %d optima, %d of size m+3, %.1fs' % (m, n_opt, n_more, time.time() - t), flush=True)
        if time.time() - start > time_limit:
            results['stopped'] = 'time limit after m=%d' % m
            break
    return results


def main():
    t0 = time.time()
    out = {'date': '2026-10-17', 'python': sys.version.split()[0], 'method': 'fractions, no sympy'}
    N = 100
    tc, states = transfer_counts(N)
    out['transfer_states'] = states
    with open(RECUR) as fh:
        r = json.load(fh)
    rc = series_quotient(r['numerator_coefficients_ascending'], r['denominator_coefficients_ascending'], N)
    with open(COUNTS) as fh:
        sc = json.load(fh)['counts']['total']
    out['three_sources_agree_0_to_100'] = (tc == rc == sc[:N + 1])
    assert tc == rc == sc[:N + 1]
    out['a3_3_to_12'] = tc[3:13]
    E = [tc[m] - 4 * (m - 1) * (3 * m + 2) * 3 ** (m - 5) if m >= 5 else None for m in range(N + 1)]
    E[4] = tc[4] - 4 * 3 * 14 // 3
    assert 4 * 3 * 14 % 3 == 0
    out['E_4_to_12'] = E[4:13]
    assert E[4:7] == [168, 620, 2220]

    A = [ansatz_row(m) for m in range(4, 16)]
    coef = solve_rational(A, [E[m] for m in range(4, 16)])
    names = ['x0', 'x1', 'x2', 'y0', 'y1', 'y2', 'p0', 'p1', 'p2', 'q0', 'q1', 'q2']
    out['solved_coefficients'] = {n: str(c) for n, c in zip(names, coef)}
    sym_path = os.path.join(DATA, 'three_row_closed_form.json')
    if os.path.exists(sym_path):
        with open(sym_path) as fh:
            sym = json.load(fh)['real_form_coefficients']
        same = all(Fraction(sym[n]) == c for n, c in zip(names, coef))
        out['coefficients_agree_with_sympy_derivation'] = same
        assert same
    mism = [m for m in range(4, N + 1) if closed_form(coef, m) != E[m]]
    out['closed_form_matches_E_m_4_to_100'] = not mism
    assert not mism
    # also for m = 2, 3 against the formal coefficients 4*AB + X of the class series
    with open(COUNTS) as fh:
        cl = json.load(fh)['counts']
    formal = [4 * a + x for a, x in zip(cl['AB'], cl['X'])]
    out['closed_form_matches_formal_E_m_2_to_3'] = all(closed_form(coef, m) == formal[m] for m in (2, 3))
    out['closed_form_fails_at_m_0_1'] = [m for m in (0, 1) if closed_form(coef, m) != formal[m]]
    out['E_positive_4_to_100'] = all(E[m] > 0 for m in range(4, N + 1))

    # paper-form check: p_+(m) = ((19+11 sqrt3) m^2 + (61+41 sqrt3) m + (104+28 sqrt3))/432
    x = [Fraction(104, 432), Fraction(61, 432), Fraction(19, 432)]
    y = [Fraction(28, 432), Fraction(41, 432), Fraction(11, 432)]
    def paper(m):
        P, Q = pq(m)
        val = 2 * sum(m ** k * (x[k] * P + 3 * y[k] * Q) for k in range(3))
        if m % 2 == 0:
            val += Fraction((-1) ** (m // 2) * 2 ** (m // 2) * (2 * m * m + 41 * m - 104), 216)
        else:
            val += Fraction((-1) ** ((m + 1) // 2) * 2 ** ((m - 1) // 2) * (-7 * m * m + 32 * m + 175), 432)
        return val
    out['paper_form_matches_E_m_2_to_100'] = all(paper(m) == E[m] for m in range(4, N + 1)) and \
        all(paper(m) == formal[m] for m in (2, 3))
    assert out['paper_form_matches_E_m_2_to_100']

    out['brute_force'] = brute_counts(7, 1500)
    out['brute_matches_transfer_3_to_7'] = all(
        out['brute_force'][m]['valid_size_m+2'] == tc[m] and out['brute_force'][m]['valid_size_m+3'] == 0
        for m in range(3, 8) if m in out['brute_force'])
    out['seconds'] = round(time.time() - t0, 1)
    os.makedirs(DATA, exist_ok=True)
    with open(os.path.join(DATA, 'three_row_closed_form_check.json'), 'w') as fh:
        json.dump(out, fh, indent=1)
    for k, v in out.items():
        if k != 'brute_force':
            print(k, v)
    print('brute_force', out['brute_force'])


if __name__ == '__main__':
    main()
