"""Recheck of the growth constant rho, the pole order and the leading constant for a_4(m).

Uses the stored factorization of Q_4 (already verified exactly by
four_row_recurrence_check.py) and the recount of a_4(m) from
four_row_dp_check.py.  Roots are located with numpy's companion-matrix
solver and then refined with mpmath Newton iteration at 80 digits; the
leading constant is evaluated from the partial fraction at the dominant pole
in high precision; the partition growth rates are compared with the ratios of
consecutive recounted terms at width 1499, which involve neither the
factorization nor any eigenvalue computation.

Results go to jis/data/four_row_rho_check.json.
"""
import json
import os
import sys
import time

import mpmath
import numpy as np
import sympy

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from four_row_recurrence_check import (DATA, NAMES, factor_exponents, expand, power,  # noqa: E402
                                       divmod_exact, mul, trim)

Z = sympy.Symbol('z')
STATED_MIN_POLY_HIGH_TO_LOW = [1, -4, 2, 1, -3, 5, 1, -3, 7, 2, 30, -7, 10, 12, 2, 17, 26, 19,
                              -26, -4, 8]
mpmath.mp.dps = 80


def roots_of(coeffs_low_to_high):
    return np.roots(np.array(coeffs_low_to_high[::-1], dtype=float))


def mp_eval(coeffs_low_to_high, x):
    return mpmath.polyval([mpmath.mpf(c) for c in coeffs_low_to_high[::-1]], x)


def mp_eval_derivative(coeffs_low_to_high, x):
    d = [i * c for i, c in enumerate(coeffs_low_to_high)][1:]
    return mp_eval(d, x)


def refine_real_root(coeffs_low_to_high, x0, steps=100):
    x = mpmath.mpf(x0)
    for _ in range(steps):
        fx = mp_eval(coeffs_low_to_high, x)
        dfx = mp_eval_derivative(coeffs_low_to_high, x)
        step = fx / dfx
        x -= step
        if abs(step) < mpmath.mpf(10) ** (-75):
            break
    return x


def main():
    t0 = time.time()
    mine = json.load(open(os.path.join(DATA, 'four_row_dp_check.json')))
    stored = json.load(open(os.path.join(DATA, 'four_row_recurrence.json')))
    width = mine['width']
    a = [int(mine['a4'][str(m)]) for m in range(width + 1)]
    per = {NAMES[k]: [int(mine['per_partition'][NAMES[k]][str(m)]) for m in range(width + 1)]
           for k in NAMES}
    Q = [int(c) for c in stored['denominator_Q4_coefficients_low_to_high']]
    P = [int(c) for c in stored['numerator_P4_coefficients_low_to_high']]
    q_exp, _ = factor_exponents(stored['denominator_Q4_factored'])
    out = {}

    # root moduli of every factor of Q_4
    table = []
    for base, e in q_exp.items():
        rts = roots_of(list(base))
        mods = sorted(abs(r) for r in rts)
        real_pos = sorted(r.real for r in rts if abs(r.imag) < 1e-9 and r.real > 0)
        table.append({'degree': len(base) - 1, 'multiplicity': e,
                      'smallest_root_modulus': float(mods[0]),
                      'second_smallest_root_modulus': float(mods[1]) if len(mods) > 1 else None,
                      'smallest_positive_real_root': float(real_pos[0]) if real_pos else None,
                      'coefficients_low_to_high': list(base)})
    table.sort(key=lambda t: t['smallest_root_modulus'])
    out['factors_by_smallest_root_modulus'] = table
    dom = table[0]
    g = dom['coefficients_low_to_high']
    out['dominant_factor_degree'] = dom['degree']
    out['dominant_factor_multiplicity'] = dom['multiplicity']
    out['dominant_root_is_real_positive'] = abs(dom['smallest_positive_real_root'] -
                                                dom['smallest_root_modulus']) < 1e-12
    out['next_root_modulus_among_all_other_roots'] = min(
        [t['smallest_root_modulus'] for t in table[1:]] + [dom['second_smallest_root_modulus']])

    # rho to 60 digits from the dominant factor, and its minimal polynomial
    z0 = refine_real_root(g, dom['smallest_positive_real_root'])
    rho = 1 / z0
    out['rho_60_digits'] = mpmath.nstr(rho, 60)
    out['rho_matches_stored_60_digits'] = (mpmath.nstr(rho, 60) == stored['rho_60_digits'][:len(mpmath.nstr(rho, 60))]
                                           or abs(rho - mpmath.mpf(stored['rho_60_digits'])) < mpmath.mpf(10) ** (-58))
    reversed_g = g[::-1]
    # the reversed factor, read from its leading coefficient down, is the stated polynomial
    out['reversed_dominant_factor_equals_stated_minimal_polynomial'] = (
        reversed_g[::-1] == STATED_MIN_POLY_HIGH_TO_LOW and reversed_g[-1] == 1)
    # all other roots of the minimal polynomial x^20 g(1/x) have modulus below rho
    xr = roots_of(reversed_g)
    others = sorted(abs(r) for r in xr)[:-1]
    out['rho_is_the_unique_root_of_largest_modulus_of_its_minimal_polynomial'] = bool(
        max(others) < float(rho) - 1e-6)
    out['largest_other_root_modulus_of_minimal_polynomial'] = float(max(others))
    out['rho_in_pre_registered_interval_3.4_to_3.8158'] = bool(3.4 <= float(rho) < 212 ** 0.25)
    out['rho_below_212_to_the_quarter'] = bool(float(rho) < 212 ** 0.25)

    # pole order and leading constant: Q_4 = g^5 rest, g = (1 - rho z) h
    rest = divmod_exact(Q, power(g, dom['multiplicity']))
    assert mul(rest, power(g, dom['multiplicity'])) == Q
    h_z0 = -mp_eval_derivative(g, z0) / rho
    A = mp_eval(P, z0) / (h_z0 ** dom['multiplicity'] * mp_eval(rest, z0))
    c = A / 24
    out['P4_at_1_over_rho_nonzero'] = bool(mp_eval(P, z0) != 0)
    out['pole_order_at_1_over_rho'] = dom['multiplicity']
    out['leading_constant_c'] = mpmath.nstr(c, 30)
    out['leading_constant_matches_stored_12_digits'] = bool(
        abs(c - mpmath.mpf(stored['leading_constant_c'])) / c < mpmath.mpf(10) ** (-11))
    out['a4_over_c_m4_rho_m'] = {str(m): mpmath.nstr(mpmath.mpf(a[m]) / (c * mpmath.mpf(m) ** 4 * rho ** m), 8)
                                 for m in (500, 1000, 1500)}
    m = width - 1
    out['ratio_test_at_width_1499'] = mpmath.nstr(mpmath.mpf(a[m + 1]) / a[m] * (mpmath.mpf(m) / (m + 1)) ** 4, 12)

    # partition growth rates: dominant singularity of each partition denominator,
    # and the ratio test on the recounted partition sequences
    part = {}
    for key, name in NAMES.items():
        exps, _ = factor_exponents(stored['per_partition'][key]['denominator_factored'])
        best = None
        for base, e in exps.items():
            rts = roots_of(list(base))
            for r in rts:
                if best is None or abs(r) < best[0]:
                    best = (abs(r), r, len(base) - 1, e, list(base))
        modulus, r, deg, e, base = best
        others = sorted(abs(x) for b in exps for x in roots_of(list(b)))
        second = others[1]
        real = abs(r.imag) < 1e-9 and r.real > 0
        zr = refine_real_root(base, r.real) if real else None
        seq = per[name]
        ratio = mpmath.mpf(seq[m + 1]) / seq[m] * (mpmath.mpf(m) / (m + 1)) ** 4
        part[name] = {'dominant_factor_degree': deg, 'multiplicity': e,
                      'dominant_root_real_positive_and_unique': bool(real and second > modulus + 1e-9),
                      'growth_rate_from_factor': mpmath.nstr(1 / zr, 15) if real else None,
                      'ratio_test_at_width_1499': mpmath.nstr(ratio, 12),
                      'share_of_optima_at_width_40': mpmath.nstr(mpmath.mpf(seq[40]) / a[40], 6)}
    out['partitions'] = part
    out['dominant_factor_carried_only_by'] = [
        n for n, t in part.items() if t['dominant_factor_degree'] == dom['degree']]
    out['seconds'] = round(time.time() - t0, 2)
    json.dump(out, open(os.path.join(DATA, 'four_row_rho_check.json'), 'w'), indent=1)
    for k, v in out.items():
        if k != 'factors_by_smallest_root_modulus':
            print(k, '->', v)
    for t in table:
        print('factor deg', t['degree'], 'mult', t['multiplicity'], 'min |root|',
              t['smallest_root_modulus'], 'real+', t['smallest_positive_real_root'])


if __name__ == '__main__':
    main()
