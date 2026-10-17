"""Exact recheck of the four-row generating function P_4/Q_4 and its factorization.

Reads the recount of a_4(m) produced by four_row_dp_check.py and the stored
polynomials in jis/data/four_row_recurrence.json, and verifies with integer
arithmetic written here (no computer algebra system except for parsing the
stored factor strings):

  1. the stored denominator Q_4 equals the product of its listed factors;
  2. sum_j q_j a_4(n-j) = 0 for every n from 445 to the end of the recount
     and not at n = 444;
  3. Q_4(z) times the series equals the stored numerator P_4 of degree 444;
  4. P_4 and Q_4 are coprime (polynomial gcd over two prime fields);
  5. each listed factor is irreducible over the integers (irreducible modulo
     a prime that does not divide its leading coefficient), the factors are
     pairwise distinct, and Q_4 is the least common multiple of the three
     partition denominators;
  6. Berlekamp-Massey modulo a prime on the recount reproduces Q_4 and the
     three partition denominators with the stated orders;
  7. the survival ratio a_4(m) / (3 (m)_4 4^(m-4)) rises from m = 6 to 7 and
     then decreases strictly through the end of the recount.

Results go to jis/data/four_row_recurrence_check.json.
"""
import json
import os
import sys
import time

import sympy

HERE = os.path.dirname(os.path.abspath(__file__))
PROBLEM = os.path.dirname(os.path.dirname(HERE))
DATA = os.path.join(PROBLEM, 'jis', 'data')
NAMES = {'01|23': '{1,2}|{3,4}', '02|13': '{1,3}|{2,4}', '03|12': '{1,4}|{2,3}'}
Z = sympy.Symbol('z')
PRIMES = [(1 << 61) - 1, (1 << 62) - 57]   # both prime


# ---- integer polynomials, coefficient lists low to high ----

def trim(p):
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p


def mul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return trim(r)


def power(p, e):
    r = [1]
    for _ in range(e):
        r = mul(r, p)
    return r


def divmod_exact(p, q):
    """Quotient of p by q over the integers; asserts that the division is exact."""
    p = list(p)
    q = trim(list(q))
    quo = [0] * max(1, len(p) - len(q) + 1)
    for i in range(len(p) - len(q), -1, -1):
        c, rem = divmod(p[i + len(q) - 1], q[-1])
        assert rem == 0, 'not exactly divisible'
        quo[i] = c
        for j, b in enumerate(q):
            p[i + j] -= c * b
    assert all(c == 0 for c in p), 'nonzero remainder'
    return trim(quo)


def from_expr(expr):
    """Low-to-high integer coefficients of a sympy polynomial in z."""
    poly = sympy.Poly(expr, Z)
    coeffs = [int(c) for c in poly.all_coeffs()]
    return trim(coeffs[::-1])


def factor_exponents(expr_string):
    """{coefficient tuple: exponent} from a sympy factored string, bases made monic in z^0 = 1."""
    expr = sympy.sympify(expr_string)
    out = {}
    sign = 1
    for arg in sympy.Mul.make_args(expr):
        base, exp = arg.as_base_exp()
        if base.is_number:
            sign *= int(base) ** int(exp)
            continue
        coeffs = from_expr(base)
        if coeffs[0] < 0:
            coeffs = [-c for c in coeffs]
            if int(exp) % 2:
                sign = -sign
        assert coeffs[0] == 1, coeffs
        out[tuple(coeffs)] = out.get(tuple(coeffs), 0) + int(exp)
    return out, sign


def expand(exponents):
    r = [1]
    for base, e in exponents.items():
        r = mul(r, power(list(base), e))
    return r


# ---- polynomials over GF(p) ----

def pmod(p, m):
    return trim([c % m for c in p])


def pmul_mod(p, q, m):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] = (r[i + j] + a * b) % m
    return trim(r)


def prem_mod(p, q, m):
    p = list(p)
    inv = pow(q[-1], -1, m)
    for i in range(len(p) - len(q), -1, -1):
        c = p[i + len(q) - 1] * inv % m
        if c:
            for j, b in enumerate(q):
                p[i + j] = (p[i + j] - c * b) % m
    return trim(p[:max(1, len(q) - 1)])


def pgcd_mod(p, q, m):
    p, q = pmod(p, m), pmod(q, m)
    while q != [0]:
        p, q = q, prem_mod(p, q, m)
    inv = pow(p[-1], -1, m)
    return [c * inv % m for c in p]


def ppow_mod(base, e, f, m):
    result = [1]
    base = prem_mod(base, f, m)
    while e:
        if e & 1:
            result = prem_mod(pmul_mod(result, base, m), f, m)
        base = prem_mod(pmul_mod(base, base, m), f, m)
        e >>= 1
    return result


def irreducible_mod(f, p):
    """Rabin's test: f of degree n is irreducible over GF(p)."""
    n = len(f) - 1
    f = pmod(f, p)
    if len(f) - 1 != n:
        return False
    x = [0, 1]
    # x^(p^n) == x mod f
    h = x
    for _ in range(n):
        h = ppow_mod(h, p, f, p)
    if trim([(a - b) % p for a, b in zip(h + [0] * 2, x + [0] * len(h))]) != [0]:
        return False
    for q in sympy.primefactors(n):
        h = x
        for _ in range(n // q):
            h = ppow_mod(h, p, f, p)
        diff = [0] * max(len(h), 2)
        for i, c in enumerate(h):
            diff[i] = c
        diff[1] = (diff[1] - 1) % p
        if trim(diff) == [0] or len(pgcd_mod(f, diff, p)) > 1:
            return False
    return True


def irreducible_over_Z(f):
    """Return a prime modulo which f is irreducible, or None after trying 60 primes."""
    n = len(f) - 1
    if n == 1:
        return 'degree 1'
    for p in list(sympy.primerange(1000, 10000))[:60]:
        if f[-1] % p == 0:
            continue
        if irreducible_mod(f, p):
            return p
    return None


def berlekamp_massey(seq, p):
    """Minimal connection polynomial (low to high, c_0 = 1) of seq modulo the prime p."""
    s = [x % p for x in seq]
    C, B = [1], [1]
    L, m, b = 0, 1, 1
    for n in range(len(s)):
        d = s[n]
        for i in range(1, L + 1):
            d = (d + C[i] * s[n - i]) % p
        if d == 0:
            m += 1
            continue
        T = list(C)
        coef = d * pow(b, -1, p) % p
        if len(C) < len(B) + m:
            C += [0] * (len(B) + m - len(C))
        for i, x in enumerate(B):
            C[i + m] = (C[i + m] - coef * x) % p
        if 2 * L <= n:
            L, B, b, m = n + 1 - L, T, d, 1
        else:
            m += 1
    return trim(C[:L + 1]), L


def main():
    t0 = time.time()
    mine = json.load(open(os.path.join(DATA, 'four_row_dp_check.json')))
    stored = json.load(open(os.path.join(DATA, 'four_row_recurrence.json')))
    width = mine['width']
    a = [int(mine['a4'][str(m)]) for m in range(width + 1)]
    per = {NAMES[k]: [int(mine['per_partition'][NAMES[k]][str(m)]) for m in range(width + 1)]
           for k in NAMES}
    Q = [int(c) for c in stored['denominator_Q4_coefficients_low_to_high']]
    P_stored = [int(c) for c in stored['numerator_P4_coefficients_low_to_high']]
    D = len(Q) - 1
    out = {'recount_width': width, 'degree_Q4': D}

    # 1. factor product
    q_exp, sign = factor_exponents(stored['denominator_Q4_factored'])
    out['Q4_equals_product_of_listed_factors'] = (expand(q_exp) == Q and sign == 1)
    out['factor_degrees_and_multiplicities'] = sorted((len(b) - 1, e) for b, e in q_exp.items())

    # 2. the recurrence on the recount
    def residuals(seq, poly):
        d = len(poly) - 1
        return [sum(poly[j] * seq[n - j] for j in range(d + 1)) for n in range(d, len(seq))]
    u = residuals(a, Q)
    nonzero = [n for n, v in zip(range(D, width + 1), u) if v != 0]
    first_good = (max(nonzero) + 1) if nonzero else D
    out['recurrence_holds_from_width'] = first_good
    out['recurrence_fails_at_444'] = any(n == 444 for n in nonzero)
    out['recurrence_checked_through_width'] = width

    # 3. numerator
    prod = mul(Q, a)
    P = trim(prod[:width + 1])
    out['numerator_degree'] = len(P) - 1
    out['numerator_matches_stored'] = (P == trim(list(P_stored)))
    out['product_vanishes_beyond_numerator'] = all(c == 0 for c in prod[445:width + 1])

    # 4. coprimality
    out['gcd_P4_Q4_degree_mod_primes'] = {str(p): len(pgcd_mod(P, Q, p)) - 1 for p in PRIMES}
    out['P4_Q4_coprime'] = all(v == 0 for v in out['gcd_P4_Q4_degree_mod_primes'].values())

    # 5. irreducibility, distinctness, lcm
    irr = {}
    for base in q_exp:
        irr[str(sympy.Poly(list(base)[::-1], Z).as_expr())] = irreducible_over_Z(list(base))
    out['factor_irreducibility_witness_prime'] = irr
    out['all_factors_irreducible'] = all(v is not None for v in irr.values())
    out['factors_pairwise_distinct'] = len(q_exp) == len(set(q_exp))
    part_exp = {}
    part_Q = {}
    for k, name in NAMES.items():
        exps, sgn = factor_exponents(stored['per_partition'][k]['denominator_factored'])
        part_exp[name] = exps
        part_Q[name] = expand(exps)
    lcm_exp = {}
    for exps in part_exp.values():
        for b, e in exps.items():
            lcm_exp[b] = max(lcm_exp.get(b, 0), e)
    out['Q4_is_lcm_of_partition_denominators'] = (lcm_exp == q_exp)
    out['partition_denominator_degrees'] = {n: len(q) - 1 for n, q in part_Q.items()}
    out['partition_denominators_divide_Q4'] = {}
    for name, q in part_Q.items():
        try:
            divmod_exact(Q, q)
            out['partition_denominators_divide_Q4'][name] = True
        except AssertionError:
            out['partition_denominators_divide_Q4'][name] = False
    shared = {}
    names = list(part_exp)
    for i in range(3):
        for j in range(i + 1, 3):
            common = set(part_exp[names[i]]) & set(part_exp[names[j]])
            shared[f'{names[i]} & {names[j]}'] = [
                str(sympy.Poly(list(b)[::-1], Z).as_expr()) for b in common]
    out['factors_shared_between_partitions'] = shared

    # partition recurrences on the recount, with their own thresholds
    part_rec = {}
    for name, q in part_Q.items():
        seq = per[name]
        d = len(q) - 1
        res = residuals(seq, q)
        nz = [n for n, v in zip(range(d, width + 1), res) if v != 0]
        prod_p = mul(q, seq)
        P_p = trim(prod_p[:width + 1])
        gcds = {str(p): len(pgcd_mod(P_p, q, p)) - 1 for p in PRIMES}
        part_rec[name] = {'denominator_degree': d, 'numerator_degree': len(P_p) - 1,
                          'recurrence_holds_from_width': (max(nz) + 1) if nz else d,
                          'coprime': all(v == 0 for v in gcds.values())}
    out['partition_recurrences'] = part_rec

    # 6. Berlekamp-Massey modulo a prime on the recount, tail indexing from width 6
    p = PRIMES[0]
    C, L = berlekamp_massey(a[6:], p)
    out['berlekamp_massey_order_total'] = L
    out['berlekamp_massey_connection_matches_Q4_mod_p'] = (trim(list(C)) == pmod(Q, p))
    bm_part = {}
    for name, seq in per.items():
        Cp, Lp = berlekamp_massey(seq[6:], p)
        bm_part[name] = {'order': Lp, 'stripped_degree': len(trim(list(Cp))) - 1,
                         'matches_partition_denominator_mod_p': trim(list(Cp)) == pmod(part_Q[name], p)}
    out['berlekamp_massey_per_partition'] = bm_part

    # 7. survival ratio, exact: r(m+1) < r(m)  iff  a(m+1) (m-3) < 4 a(m) (m+1)
    rises = [m for m in range(6, width) if a[m + 1] * (m - 3) > 4 * a[m] * (m + 1)]
    ties = [m for m in range(6, width) if a[m + 1] * (m - 3) == 4 * a[m] * (m + 1)]
    out['survival_ratio_rises_at'] = rises
    out['survival_ratio_ties_at'] = ties
    out['survival_ratio_strictly_decreasing_from_7'] = (rises == [6] and not ties)

    out['seconds'] = round(time.time() - t0, 2)
    json.dump(out, open(os.path.join(DATA, 'four_row_recurrence_check.json'), 'w'), indent=1)
    for k, v in out.items():
        print(k, '->', v)


if __name__ == '__main__':
    main()
