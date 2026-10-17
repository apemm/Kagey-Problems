"""Closed form of the three-row remainder E_m (sympy route).

For m >= 4 the number a_3(m) of maximum blackouts of the 3 x m grid is

    a_3(m) = 4 (m-1)(3m+2) 3^(m-5) + E_m,

where the dominant term counts the two ordered classes with doubles {A, C} and
E_m = 4 AB_m + X_m counts the four ordered outer-pair classes and the triple class.
The class generating functions G_AC, G_AB, G_X are rebuilt here from the run and
interface formulas of the structural derivation (scalar run functions g0, g1, u, v,
the endpoint kernel J, and the gap decomposition), compared with the stored sympy
strings of the research archive, and then E(z) = 4 G_AB + G_X is decomposed into
partial fractions over Q(sqrt 3) and Q(i sqrt 2) by solving the linear system of the
ansatz

    E_m = p_+(m) rho^m + p_-(m) sigma^m + q(m) (i sqrt2)^m + conj(q)(m) (-i sqrt2)^m,

rho = 1 + sqrt3, sigma = 1 - sqrt3, with quadratic coefficient polynomials.  The
identity is then proved in two ways: symbolically, by clearing denominators of the
generating function of the ansatz, and by the order-12 recurrence of the denominator
(1-2z-2z^2)^3 (1+2z^2)^3 together with twelve consecutive initial values.

Output: jis/data/three_row_closed_form.json (coefficients as exact rationals, the
first values, the proof flags, the positivity threshold).
"""
import json
import math
import os
import sys
import time

import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(os.path.dirname(HERE), 'data')
ARCHIVE = os.path.join(os.path.expanduser('~'), 'Downloads', 'Problem 001 Research 2026-10-16',
                       'research_notes', 'Problem 001 structural improvements', 'three_row',
                       'verification_results.json')

z = sp.symbols('z')


def class_functions():
    """G_AC, G_AB, G_X from the run and interface formulas (hand derivation)."""
    R = 1 - 3 * z
    L = 1 - 2 * z - 2 * z ** 2
    N = 1 + 2 * z ** 2
    D = L * N
    g0 = z * (1 + z + 3 * z ** 2 + 2 * z ** 3) / D
    g1 = z * (1 + z) / D
    u = z * (1 + 2 * z ** 2 + 2 * z ** 3) / D
    v = z / D
    G_X = z * (1 + 4 * u + 2 * v + 2 * u ** 2 + v ** 2)
    la, lb, lc = 1 + 2 * u + v, 1 + u, 1 + 2 * u
    ra, rb, rc = 1 + g0, 1 + g0 + g1, 1 + g0 + g1
    J = sp.Matrix([[1 + 2 * z ** 2 + 2 * z ** 3, z + z ** 2], [1, 2 * z ** 2 + 2 * z ** 3]]) / D
    left = sp.Matrix([[la + lc, lb]])
    right = sp.Matrix([ra + rc, 2 * rb])
    G_AB = (z ** 2 * (1 + 2 * u) * (1 + g0 + g1)
            + z ** 3 * (la * ra + lb * rb + lc * rc)
            + z ** 4 * (left * J * right)[0, 0])
    G_AC = (z ** 2 * (1 + z / R) ** 2
            + z ** 3 * (3 + 12 * z / R + 13 * z ** 2 / R ** 2)
            + 9 * z ** 4 * (1 - z) ** 2 / R ** 3)
    return sp.cancel(G_AC), sp.cancel(G_AB), sp.cancel(G_X)


def series_coeffs(expr, n):
    s = sp.series(expr, z, 0, n + 1).removeO()
    p = sp.Poly(s, z)
    return [int(p.coeff_monomial(z ** k)) for k in range(n + 1)]


def main():
    t0 = time.time()
    out = {'date': '2026-10-17', 'python': sys.version.split()[0], 'sympy': sp.__version__,
           'coordinates': 'not applicable (generating functions only)'}

    G_AC, G_AB, G_X = class_functions()
    out['class_generating_functions_rebuilt'] = {'AC': str(G_AC), 'AB': str(G_AB), 'X': str(G_X)}

    # comparison with the archive's stored sympy strings
    if os.path.exists(ARCHIVE):
        with open(ARCHIVE) as fh:
            stored = json.load(fh)['class_generating_functions']
        agree = {k: bool(sp.simplify(sp.sympify(stored[k]) - g) == 0)
                 for k, g in (('AC', G_AC), ('AB', G_AB), ('X', G_X))}
        out['rebuilt_equals_archive_strings'] = agree
        assert all(agree.values()), agree
    else:
        out['rebuilt_equals_archive_strings'] = 'archive file not found'

    # dominant term
    ac = series_coeffs(G_AC, 40)
    dominant_ok = all(ac[m] == 2 * (m - 1) * (3 * m + 2) * 3 ** (m - 5) for m in range(4, 41))
    out['AC_coefficient_equals_2(m-1)(3m+2)3^(m-5)_for_4<=m<=40'] = dominant_ok
    assert dominant_ok

    E = sp.cancel(4 * G_AB + G_X)
    num, den = sp.fraction(E)
    out['E_numerator'] = str(sp.expand(num))
    out['E_denominator'] = str(sp.factor(den))
    L = 1 - 2 * z - 2 * z ** 2
    N = 1 + 2 * z ** 2
    assert sp.expand(den - sp.expand(L ** 3 * N ** 3)) == 0 or sp.simplify(den / (L ** 3 * N ** 3)).is_number
    e = series_coeffs(E, 100)
    out['E_m_4_to_12'] = e[4:13]
    out['E_4_5_6'] = e[4:7]
    assert e[4:7] == [168, 620, 2220]
    pol, _ = sp.div(sp.Poly(num, z), sp.Poly(den, z))
    out['polynomial_part_degree'] = int(pol.degree())

    # ansatz in real form:
    # E_m = 2 sum_k m^k (x_k P_m + 3 y_k Q_m) + [m even] 2 (-2)^(m/2) sum_k p_k m^k
    #       + [m odd] (-4)(-2)^((m-1)/2) sum_k q_k m^k
    # where rho^m = P_m + Q_m sqrt3, i.e. p_+(m) = sum (x_k + y_k sqrt3) m^k,
    # p_-(m) = sum (x_k - y_k sqrt3) m^k, q(m) = sum (p_k + q_k i sqrt2) m^k.
    xs = sp.symbols('x0:3')
    ys = sp.symbols('y0:3')
    ps = sp.symbols('p0:3')
    qs = sp.symbols('q0:3')
    unknowns = list(xs) + list(ys) + list(ps) + list(qs)

    def PQ(m):
        P, Q = 1, 0
        for _ in range(m):
            P, Q = P + 3 * Q, P + Q
        return P, Q

    def ansatz(m):
        P, Q = PQ(m)
        val = 2 * sum(m ** k * (xs[k] * P + 3 * ys[k] * Q) for k in range(3))
        if m % 2 == 0:
            val += 2 * (-2) ** (m // 2) * sum(ps[k] * m ** k for k in range(3))
        else:
            val += -4 * (-2) ** ((m - 1) // 2) * sum(qs[k] * m ** k for k in range(3))
        return val

    eqs = [sp.Eq(ansatz(m), e[m]) for m in range(4, 16)]
    sol = sp.solve(eqs, unknowns, dict=True)
    assert len(sol) == 1
    sol = sol[0]
    assert all(v.is_Rational for v in sol.values())
    out['real_form_coefficients'] = {str(k): str(sol[k]) for k in unknowns}

    s3 = sp.sqrt(3)
    is2 = sp.I * sp.sqrt(2)
    p_plus = [sol[xs[k]] + sol[ys[k]] * s3 for k in range(3)]
    p_minus = [sol[xs[k]] - sol[ys[k]] * s3 for k in range(3)]
    q_c = [sol[ps[k]] + sol[qs[k]] * is2 for k in range(3)]
    out['p_plus'] = {'degree': 2, 'coefficients_m0_m1_m2': [str(c) for c in p_plus],
                     'leading_coefficient_numeric': float(p_plus[2])}
    out['p_minus'] = {'degree': 2, 'coefficients_m0_m1_m2': [str(c) for c in p_minus]}
    out['q_complex'] = {'degree': 2, 'coefficients_m0_m1_m2': [str(c) for c in q_c],
                        'convention': 'E_m includes q(m)(i sqrt2)^m + conj(q)(m)(-i sqrt2)^m'}
    assert p_plus[2] > 0
    out['leading_coefficient_positive'] = True
    out['degrees'] = {'p_plus': int(max(k for k in range(3) if p_plus[k] != 0)),
                      'p_minus': int(max(k for k in range(3) if p_minus[k] != 0)),
                      'q': int(max(k for k in range(3) if q_c[k] != 0))}

    m = sp.symbols('m', integer=True)
    closed = (sum(p_plus[k] * m ** k for k in range(3)) * (1 + s3) ** m
              + sum(p_minus[k] * m ** k for k in range(3)) * (1 - s3) ** m
              + sum(q_c[k] * m ** k for k in range(3)) * is2 ** m
              + sum(sp.conjugate(q_c[k]) * m ** k for k in range(3)) * (-is2) ** m)
    out['closed_form_sympy'] = str(closed)

    # proof 1: generating function of the ansatz equals E(z) minus its polynomial part
    def gf_poly_times_power(coeffs, alpha):
        # sum_{m>=0} (c0 + c1 m + c2 m^2) alpha^m z^m
        w = alpha * z
        return (coeffs[0] / (1 - w) + coeffs[1] * w / (1 - w) ** 2
                + coeffs[2] * w * (1 + w) / (1 - w) ** 3)

    ansatz_gf = (gf_poly_times_power(p_plus, 1 + s3) + gf_poly_times_power(p_minus, 1 - s3)
                 + gf_poly_times_power(q_c, is2)
                 + gf_poly_times_power([sp.conjugate(c) for c in q_c], -is2))
    # the closed form is claimed for m >= 2; correct the coefficients at m = 0, 1
    corr = sum((e[k] - closed.subs(m, k)) * z ** k for k in range(2))
    diff = sp.simplify(sp.cancel(sp.expand(ansatz_gf + corr - E)))
    out['symbolic_identity_cleared_denominators'] = bool(diff == 0)
    assert diff == 0, diff

    # proof 2: order-12 recurrence with 12 consecutive initial values
    denom = sp.Poly(sp.expand(L ** 3 * N ** 3), z)
    dc = [int(denom.coeff_monomial(z ** k)) for k in range(13)]
    rec_ok = all(sum(dc[j] * e[k - j] for j in range(13)) == 0 for k in range(14, 101))
    closed_vals = [sp.nsimplify(sp.expand(closed.subs(m, k))) for k in range(0, 30)]
    init_ok = all(closed_vals[k] == e[k] for k in range(2, 14))
    rec_closed = all(sum(dc[j] * closed_vals[k - j] for j in range(13)) == 0 for k in range(12, 30))
    out['recurrence_proof'] = {'denominator_coefficients_ascending': dc,
                               'E_satisfies_recurrence_14<=m<=100': rec_ok,
                               'closed_form_matches_E_2<=m<=13': init_ok,
                               'closed_form_satisfies_recurrence_sample': rec_closed}
    assert rec_ok and init_ok and rec_closed
    out['closed_form_equals_E_m_for_0<=m<=29'] = [int(k) for k in range(30) if closed_vals[k] != e[k]]
    out['closed_form_valid_from'] = 2

    # the real period-4 form of the (i sqrt2)^m part
    xq = [sol[ps[k]] for k in range(3)]
    yq = [sol[qs[k]] for k in range(3)]
    out['period4_part'] = {
        'even_m': 'E_m includes (-1)^(m/2) 2^(m/2+1) (%s + (%s) m + (%s) m^2)' % tuple(str(c) for c in xq),
        'odd_m': 'E_m includes (-1)^((m+1)/2) 2^((m+3)/2) (%s + (%s) m + (%s) m^2)' % tuple(str(c) for c in yq)}

    # positivity: for m >= M1, p_+(m) >= (a2/2) m^2 (quadratic inequality, exact);
    # |p_-(m) sigma^m| + |tau part| <= C m^2 2^(m/2) with |sigma| < 1 <= 2^(m/2);
    # so E_m > 0 once (rho/sqrt2)^m > 2C/a2, and the finitely many m below are checked.
    a2, a1, a0 = p_plus[2], p_plus[1], p_plus[0]
    M1 = 4
    while not (a2 * M1 ** 2 / 2 + a1 * M1 + a0 >= 0 and a2 * M1 / 2 * 2 + a1 >= 0):
        M1 += 1          # beyond M1 the quadratic a2 m^2/2 + a1 m + a0 is increasing and >= 0
    C_up = sum(abs(float(c)) for c in p_minus) + 2 * sum(abs(complex(c)) for c in q_c)
    M2 = math.ceil(math.log(2 * C_up / float(a2)) / math.log((1 + math.sqrt(3)) / math.sqrt(2))) + 1
    M0 = max(M1, M2, 4)
    direct = all(e[k] > 0 for k in range(4, M0 + 1))
    out['positivity'] = {'M1_from_which_p_plus(m)>=a2*m^2/2': int(M1),
                         'upper_bound_constant_C': C_up,
                         'M2_from_which_(rho/sqrt2)^m>2C/a2': int(M2),
                         'threshold_M0': int(M0),
                         'E_m_positive_directly_for_4<=m<=M0': direct,
                         'statement': 'E_m > 0 for all m >= 4'}
    assert direct

    # asymptotics
    out['asymptotic'] = {'E_m ~ c m^2 rho^m with c': str(p_plus[2]),
                         'c_numeric': float(p_plus[2]), 'rho': '1+sqrt(3)'}
    out['E_m_0_to_100'] = e
    out['seconds'] = round(time.time() - t0, 2)

    os.makedirs(DATA, exist_ok=True)
    with open(os.path.join(DATA, 'three_row_closed_form.json'), 'w') as fh:
        json.dump(out, fh, indent=1)
    print('E_4..E_12 =', e[4:13])
    print('p_+ coefficients (m^0, m^1, m^2):', [str(c) for c in p_plus])
    print('p_- coefficients:', [str(c) for c in p_minus])
    print('q coefficients:', [str(c) for c in q_c])
    print('period-4 part:', out['period4_part'])
    print('symbolic identity:', out['symbolic_identity_cleared_denominators'])
    print('recurrence proof:', out['recurrence_proof'])
    print('positivity:', out['positivity'])
    print('seconds', out['seconds'])


if __name__ == '__main__':
    main()
