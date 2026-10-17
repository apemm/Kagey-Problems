"""Minimal linear recurrence of a_4(m), its certificate, and the growth constant.

Input: jis/data/four_row_counts.json (from four_row_counts.py) and the three
exported geometry machines.

Steps.
1. Guess.  Berlekamp-Massey modulo several 62-bit primes on the tail
   b_k = a_4(6+k), k >= 0 (and separately on each partition's own sequence); the
   connection polynomial is lifted to integers by the Chinese remainder theorem
   (the denominator divides a characteristic polynomial with constant term 1, so
   its coefficients are integers) and checked exactly on every stored term.
2. Certify.  For each partition, the product automaton has states (U, s) with U a
   subset of the four double letters and s a geometry state; T is its transfer
   operator and v(n) = v(0) T^n the vector of word counts after n columns.  If
   sum_j q_j v(K-j) = 0 in every coordinate for one K, then applying T^r to that
   identity gives it for every K+r, and the accepting functional (sum over U =
   all four doubles) turns it into the scalar recurrence sum_j q_j c(n-j) = 0 for
   every n >= K, where c(n) = a_4(n) for n >= 6 and c(n) = 0 for n <= 5.  The
   script records the least such K per partition.
3. Growth.  Factor Q over the integers (sympy), locate the largest real root
   1/rho, its multiplicity (the pole order), the minimal polynomial of rho, rho to
   high precision, the leading constant of a_4(m) ~ c m^(k-1) rho^m, and which
   partition's denominator carries the dominant factor.
4. The survival ratio a_4(m) / (3 (m)_4 4^(m-4)) is checked for monotone decrease
   from m = 7 on with exact rational arithmetic.

Writes jis/data/four_row_recurrence.json.
"""
import json
import os
import sys
import time
from fractions import Fraction

import sympy
from sympy import Poly, Rational, factor_list, symbols

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from four_row_machines import load_all  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "data")
PRIMES = [4611686018427387847, 4611686018427387817, 4611686018427387787,
          4611686018427387761, 4611686018427387751, 4611686018427387737,
          4611686018427387733, 4611686018427387709]  # the 8 largest primes below 2^62


def berlekamp_massey(seq, p):
    """Connection polynomial C (C[0]=1) and order L of seq modulo prime p."""
    C = [1]
    B = [1]
    L = 0
    m = 1
    b = 1
    for n in range(len(seq)):
        d = seq[n] % p
        for i in range(1, L + 1):
            d = (d + C[i] * seq[n - i]) % p
        if d == 0:
            m += 1
            continue
        T = C[:]
        coef = d * pow(b, p - 2, p) % p
        if len(C) < len(B) + m:
            C += [0] * (len(B) + m - len(C))
        for i in range(len(B)):
            C[i + m] = (C[i + m] - coef * B[i]) % p
        if 2 * L <= n:
            L = n + 1 - L
            B = T
            b = d
            m = 1
        else:
            m += 1
    return C[:L + 1], L


def crt_symmetric(residues, primes):
    x = 0
    M = 1
    for r, p in zip(residues, primes):
        t = ((r - x) * pow(M, -1, p)) % p
        x += M * t
        M *= p
    if x > M // 2:
        x -= M
    return x


def guess_recurrence(seq, label):
    """Integer connection polynomial q (q[0]=1) of seq, verified exactly."""
    t0 = time.time()
    polys = []
    for p in PRIMES:
        C, L = berlekamp_massey(seq, p)
        polys.append((C, L))
    Ls = {L for _, L in polys}
    assert len(Ls) == 1, (label, Ls)
    L = Ls.pop()
    q = [crt_symmetric([C[i] for C, _ in polys], PRIMES) for i in range(L + 1)]
    assert q[0] == 1
    # exact verification on every available term
    for n in range(L, len(seq)):
        assert sum(q[i] * seq[n - i] for i in range(L + 1)) == 0, (label, n)
    # Berlekamp-Massey's L is max(deg Q, deg P + 1); strip trailing zeros so that
    # q is the denominator itself and len(q) - 1 its degree
    while q[-1] == 0:
        q.pop()
    degQ = len(q) - 1
    for n in range(L, len(seq)):
        assert sum(q[i] * seq[n - i] for i in range(degQ + 1)) == 0, (label, n)
    print(f"{label}: BM order {L}, denominator degree {degQ}, verified exactly on "
          f"terms {L}..{len(seq) - 1} ({len(seq) - L} checks), max |coeff| "
          f"{max(abs(c) for c in q)}, {time.time() - t0:.1f} s", flush=True)
    return q, L


def product_operator(machine):
    """Transitions of the product automaton as a list of (src, dst) per letter."""
    trans = machine["transitions"]
    n = machine["state_count"]
    moves = []  # (U, s) -> list of (U', t)
    for U in range(16):
        for s in range(n):
            out = []
            row = trans[s]
            for k in range(8):
                t = row[k]
                if t < 0:
                    continue
                if k >= 4:
                    bit = 1 << (k - 4)
                    if U & bit:
                        continue
                    out.append((U | bit) * n + t)
                else:
                    out.append(U * n + t)
            moves.append(out)
    return moves, 16 * n


def certify(machine, q, name, max_K=4000):
    """Least K with sum_j q_j v(K-j) = 0 in all coordinates; v(n) = v(0) T^n."""
    t0 = time.time()
    moves, dim = product_operator(machine)
    d = len(q) - 1
    n = machine["state_count"]
    v = {0: 1}  # sparse: (U*n + s) -> count ; start (U=0, s=0)
    history = [v]
    K = None
    for step in range(1, max_K + 1):
        nxt = {}
        for i, c in v.items():
            for j in moves[i]:
                nxt[j] = nxt.get(j, 0) + c
        v = nxt
        history.append(v)
        if len(history) > d + 1:
            history.pop(0)
        if step >= d:
            # history[-1] = v(step), history[-1-j] = v(step-j)
            acc = {}
            for j in range(d + 1):
                for i, c in history[-1 - j].items():
                    acc[i] = acc.get(i, 0) + q[j] * c
            if all(x == 0 for x in acc.values()):
                K = step
                break
    assert K is not None, f"{name}: no annihilation through K={max_K}"
    # count the coordinates actually involved (reachable product states)
    reach = set()
    frontier = {0}
    while frontier:
        reach |= frontier
        frontier = {j for i in frontier for j in moves[i]} - reach
    accept = sum(1 for i in reach if i // n == 15)
    print(f"{name}: all-coordinate annihilation at K = {K} (product states {dim}, "
          f"reachable {len(reach)}, accepting {accept}), {time.time() - t0:.1f} s",
          flush=True)
    return K, dim, len(reach), accept


def poly_str(coeffs, z):
    return sum(c * z ** i for i, c in enumerate(coeffs))


def main():
    t0 = time.time()
    with open(os.path.join(DATA, "four_row_counts.json")) as f:
        cnt = json.load(f)
    W = cnt["max_width"]
    total = [int(cnt["a4"][str(w)]) for w in range(W + 1)]
    per = {name: [int(cnt["per_partition"][name][str(w)]) for w in range(W + 1)]
           for name in cnt["partitions_zero_based_rows"]}
    tail = total[6:]
    q, L = guess_recurrence(tail, "total a_4(m), m >= 6")
    per_q = {}
    for name, seq in per.items():
        per_q[name] = guess_recurrence(seq[6:], f"partition {name}")

    z = symbols("z")
    Q = Poly(poly_str(q, z), z)
    # numerator of sum_{m>=6} a_4(m) z^m = P / Q  (as a series in z)
    series = [0] * 6 + tail
    prod = [sum(q[i] * series[n - i] for i in range(min(n, len(q) - 1) + 1))
            for n in range(len(series))]
    # prod must vanish from some index on (it does, by the verified recurrence)
    degP = max(i for i, c in enumerate(prod) if c != 0)
    assert all(c == 0 for c in prod[degP + 1:])
    P = Poly(poly_str(prod[:degP + 1], z), z)
    g = sympy.gcd(P, Q)
    assert g.degree() == 0, "numerator and denominator are not coprime"

    # certificate on each partition's product automaton with the total Q
    machines = dict(load_all())
    cert = {}
    for name, m in machines.items():
        K, dim, reach, accept = certify(m, q, name)
        cert[name] = {"K": K, "product_states": dim, "reachable_states": reach,
                      "reachable_accepting_states": accept}
    K_total = max(c["K"] for c in cert.values())
    # the scalar recurrence holds for every width n >= K_total; also recheck it
    for n in range(K_total, W + 1):
        assert sum(q[i] * total[n - i] for i in range(len(q))) == 0
    assert sum(q[i] * total[K_total - 1 - i] for i in range(len(q))) != 0

    # factorisation and growth
    const, factors = factor_list(Q.as_expr(), z)
    assert const in (1, -1)
    fac_info = []
    best = None
    for f, mult in factors:
        fp = Poly(f, z)
        roots = sympy.Poly(fp, z).nroots(n=30)
        real_pos = [r for r in roots if abs(sympy.im(r)) < 1e-20 and sympy.re(r) > 0]
        fac_info.append({"factor": str(f), "degree": fp.degree(), "multiplicity": mult,
                         "smallest_positive_real_root": str(min(real_pos)) if real_pos else None})
        for r in real_pos:
            if best is None or sympy.re(r) < best[0]:
                best = (sympy.re(r), f, mult, fp)
    r_min, dom_factor, pole_order, dom_poly = best
    # rho = 1/r_min; its minimal polynomial is the reversed dominant factor
    rev = Poly(list(reversed(dom_poly.all_coeffs())), z)
    rev_primitive = sympy.Poly(rev.as_expr(), z)
    if rev_primitive.LC() < 0:
        rev_primitive = -rev_primitive
    rho = sympy.nsolve(rev_primitive.as_expr(), z, 1 / r_min, prec=60)
    rho = sympy.Float(rho, 60)
    # leading constant: a_4(m) ~ c m^(k-1) rho^m, c = lim (1 - rho z)^k P/Q / (k-1)!
    k = pole_order
    rest = Q.as_expr() / (1 - rho * z) ** k   # exact after cancellation?  use numerics
    # numeric limit by high-precision evaluation of P/(Q/(1-rho z)^k) at z = 1/rho
    Qdiv = sympy.div(Q.as_expr() * 1, (1 - r_min ** -1 * z) ** k, z)
    # safer: evaluate derivative-free via polynomial division with exact root approx
    zz = 1 / rho
    # Q(z) = (1 - rho z)^k * Qrest(z); evaluate Qrest at zz by k-fold limit via
    # L'Hopital on the dominant factor: Qrest(zz) = Q^{(k)}(zz) / (k! (-rho)^k)
    Qk = sympy.diff(Q.as_expr(), z, k).subs(z, zz)
    Qrest = Qk / (sympy.factorial(k) * (-rho) ** k)
    c_lead = sympy.N(P.as_expr().subs(z, zz) / Qrest / sympy.factorial(k - 1), 30)

    # which partitions carry the dominant factor
    carriers = []
    for name, (qf, Lf) in per_q.items():
        Qf = Poly(poly_str(qf, z), z)
        rem = sympy.rem(Qf, dom_poly)
        if rem.is_zero:
            # multiplicity in Qf
            mm = 0
            cur = Qf
            while True:
                quo, r2 = sympy.div(cur, dom_poly)
                if not r2.is_zero:
                    break
                mm += 1
                cur = quo
            carriers.append({"partition": name, "multiplicity": mm})
    # numeric cross-check of rho from the terms: ratio corrected for m^(k-1)
    m = W - 1
    ratio = Fraction(total[m + 1], total[m]) * Fraction(m, m + 1) ** (k - 1)
    ratio_f = float(ratio)
    # survival ratio check
    def falling(mm):
        return mm * (mm - 1) * (mm - 2) * (mm - 3)
    surv = [Fraction(total[mm], 3 * falling(mm) * 4 ** (mm - 4)) for mm in range(6, W + 1)]
    decreasing_from_7 = all(surv[i + 1] < surv[i] for i in range(1, len(surv) - 1))
    first_violation = None
    for i in range(1, len(surv) - 1):
        if not surv[i + 1] < surv[i]:
            first_violation = 6 + i
            break
    surv_tbl = {str(mm): float(surv[mm - 6]) for mm in range(6, 41)}

    per_deg = {}
    for name, (qf, Lf) in per_q.items():
        seqf = [0] * 6 + per[name][6:]
        prodf = [sum(qf[i] * seqf[n - i] for i in range(min(n, len(qf) - 1) + 1))
                 for n in range(len(seqf))]
        per_deg[name] = {"denominator_degree": len(qf) - 1,
                         "numerator_degree": max(i for i, c in enumerate(prodf) if c != 0),
                         "berlekamp_massey_order": Lf}
    out = {
        "sequence_offset": "b_k = a_4(6+k); c(n) = a_4(n) for n >= 6, c(n) = 0 for n <= 5",
        "order": len(q) - 1,
        "order_note": "order = degree of the minimal denominator Q4; Berlekamp-Massey "
                      "reports max(deg Q4, deg P4 + 1) in tail indexing",
        "berlekamp_massey_order": L,
        "per_partition_degrees": per_deg,
        "denominator_Q4_coefficients_low_to_high": [str(c) for c in q],
        "denominator_Q4_factored": str(sympy.factor(Q.as_expr())),
        "numerator_P4_degree": degP,
        "numerator_P4_coefficients_low_to_high": [str(c) for c in prod[:degP + 1]],
        "numerator_denominator_coprime": True,
        "generating_function": "sum_{m>=6} a_4(m) z^m = P4(z)/Q4(z)",
        "guess_method": "Berlekamp-Massey modulo %d primes near 2^62, CRT lift, "
                        "exact integer verification on all stored terms" % len(PRIMES),
        "terms_available": len(tail),
        "terms_verified_after_order": len(tail) - L,
        "per_partition": {name: {"order": len(qf) - 1, "berlekamp_massey_order": Lf,
                                 "denominator_factored": str(sympy.factor(poly_str(qf, z))),
                                 "denominator_coefficients_low_to_high": [str(c) for c in qf]}
                          for name, (qf, Lf) in per_q.items()},
        "certificate": cert,
        "certificate_statement": "for each partition, sum_j q_j v(K-j) = 0 in every "
                                 "coordinate of the product automaton; hence the scalar "
                                 "recurrence holds for every width n >= %d" % K_total,
        "recurrence_threshold_width": K_total,
        "factors": fac_info,
        "dominant_factor": str(dom_factor),
        "pole_order_at_1_over_rho": pole_order,
        "rho_minimal_polynomial": str(rev_primitive.as_expr()),
        "rho_minimal_polynomial_degree": rev_primitive.degree(),
        "rho_60_digits": str(rho),
        "rho_12_digits": str(sympy.Float(rho, 13)),
        "leading_constant_c": str(c_lead),
        "asymptotic": "a_4(m) ~ c m^%d rho^m" % (pole_order - 1),
        "rho_from_terms_at_width_%d" % m: ratio_f,
        "dominant_factor_carried_by": carriers,
        "survival_ratio_decreasing_from_7_through_%d" % W: decreasing_from_7,
        "survival_ratio_first_violation": first_violation,
        "survival_ratio_6_to_40": surv_tbl,
        "sympy_version": sympy.__version__,
        "seconds": round(time.time() - t0, 1),
    }
    with open(os.path.join(DATA, "four_row_recurrence.json"), "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps({k: v for k, v in out.items()
                      if k not in ("denominator_Q4_coefficients_low_to_high",
                                   "numerator_P4_coefficients_low_to_high",
                                   "survival_ratio_6_to_40", "per_partition")}, indent=1))


if __name__ == "__main__":
    main()
