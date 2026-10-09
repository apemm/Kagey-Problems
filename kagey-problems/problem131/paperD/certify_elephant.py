"""Certified computations for the elephant walk in Paper D.

Part 1 (Lemma 3.7, Proposition 3.8 and Corollary 3.6). For every even 8 <= N < 1688
the script evaluates R_N = C_N/E_N at eps = 2/(N+2) in IEEE 754 double precision,
by the recursion that Lemma 3.7 analyzes, and adds the rounding bound of that
lemma. Here C_N = f_N(h) and E_N = f_N(0)/2, with h = N/2 and f_t(b) = P_+(M_t = b).
At eps = 2/(N+2) the transition probabilities are ratios of integers,

    1 - r_t(b) = (N(t-b) + 2b) / ((N+2)t),      r_t(b) = (2(t-b) + N b) / ((N+2)t),

and the recursion is

    f_(t+1)(b) = f_t(b) (1 - r_t(b)) + f_t(b-1) r_t(b-1),      0 <= b <= min(t, h).

The numerators and the denominator are integers below 2^53, so they are exact
in double precision. Each step then makes one division, one multiplication and
at most one addition on each term, all with positive operands and nothing else.
So the computed value of f_N(b) is the true value times a factor between
(1-u)^(3(N-1)) and (1+u)^(3(N-1)), with u = 2^-53, provided no operation
underflows. The final division adds one more rounding, and the true ratio is at
most the computed one times (1-u)^-(6N-5) <= 1 + 3e-12 for N < 1688. The script
checks that every computed quantity is at least 1e-290, so that no underflow
occurs, and it never adds, subtracts or fuses anything else.

Independent checks. (i) The same recursion in plain Python floats, entry by
entry, gives the same bits as the numpy version for a sample of N. (ii) For 20
values of N, including the one with the largest ratio, the recursion is run in
exact integer arithmetic (the numerators only, since the denominators cancel in
C_N/E_N), which decides C_N < E_N exactly and confirms the rounding bound.

Part 2 (Lemma 3.11). The Landau density is
f_L(l) = (1/pi) int_0^oo exp(-t log t - l t) sin(pi t) dt. With ball arithmetic
(python-flint, acb.integral on [2^-20, 30], plus explicit bounds for the 2 ends)
the script certifies f_L'(-0.2229) > 0 > f_L'(-0.2227) and f_L'' < -0.078 on
[-0.2229, -0.2227], and it prints enclosures of the mode and of f_L'' there.

Run with python -B certify_elephant.py. It takes about one minute.
"""
import sys
import time
from fractions import Fraction

import numpy as np

U = 2.0 ** -53
N_MAX = 1688                 # Corollary 3.6 is proved by hand for even N >= 1688
FLOOR = 1e-290               # every computed quantity must stay above this
FAILS = []


def check(label, ok, detail):
    print(('  ok    ' if ok else '  FAIL  ') + label + ': ' + detail, flush=True)
    if not ok:
        FAILS.append(label)


# ---------------------------------------------------------------- Part 1: C_N/E_N at eps = 2/(N+2)

def ratio_numpy(N):
    """Computed value of C_N/E_N at eps = 2/(N+2), and the smallest quantity met.
    Only the operations counted in Lemma 3.7 are used: for each term one division
    (the weight), one multiplication and at most one addition."""
    h = N // 2
    p = np.zeros(h + 1, dtype=np.float64)
    p[0] = 1.0                                           # f_1(0) = 1
    smallest = 1.0
    for t in range(1, N):
        L = min(t, h + 1)                                # at time t the states are 0..t-1; we keep b <= h
        b = np.arange(L, dtype=np.int64)
        stay_num = (N * (t - b) + 2 * b).astype(np.float64)     # exact integers
        up_num = (2 * (t - b) + N * b).astype(np.float64)       # exact integers
        den = float((N + 2) * t)                                 # exact integer
        w_stay = stay_num / den                          # one rounding
        w_up = up_num / den                              # one rounding
        stay = p[:L] * w_stay                            # one rounding
        up = p[:L] * w_up                                # one rounding
        new = np.zeros(h + 1, dtype=np.float64)
        new[0] = stay[0]                                 # f_(t+1)(0), no addition
        if L > 1:
            new[1:L] = stay[1:] + up[:-1]                # one rounding
        if L <= h:
            new[L] = up[L - 1]                           # f_(t+1)(t), no addition
        smallest = min(smallest, float(w_stay.min()), float(w_up.min()), float(stay.min()),
                       float(up.min()), float(new[:min(t + 1, h + 1)].min()))
        p = new
    return 2.0 * (p[h] / p[0]), smallest                 # one rounding, and an exact doubling


def ratio_python(N):
    """The same operations in the same order with plain Python floats."""
    h = N // 2
    p = [0.0] * (h + 1)
    p[0] = 1.0
    for t in range(1, N):
        L = min(t, h + 1)
        den = float((N + 2) * t)
        stay = [0.0] * L
        up = [0.0] * L
        for b in range(L):
            stay[b] = p[b] * (float(N * (t - b) + 2 * b) / den)
            up[b] = p[b] * (float(2 * (t - b) + N * b) / den)
        new = [0.0] * (h + 1)
        new[0] = stay[0]
        for b in range(1, L):
            new[b] = stay[b] + up[b - 1]
        if L <= h:
            new[L] = up[L - 1]
        p = new
    return 2.0 * (p[h] / p[0])


def ratio_exact(N):
    """C_N/E_N at eps = 2/(N+2) as an exact fraction. The common denominators
    (N+2)t cancel in f_N(h)/f_N(0), so only the integer numerators are needed."""
    h = N // 2
    g = [0] * (h + 1)
    g[0] = 1
    for t in range(1, N):
        L = min(t, h + 1)
        new = [0] * (h + 1)
        for b in range(L):
            gb = g[b]
            new[b] += gb * (N * (t - b) + 2 * b)
            if b + 1 <= h:
                new[b + 1] += gb * (2 * (t - b) + N * b)
        g = new
    return Fraction(2 * g[h], g[0])


def part1():
    print('Part 1. C_N/E_N at eps = 2/(N+2) for every even 8 <= N < 1688 (Lemma 3.7, Proposition 3.8)', flush=True)
    # The integers N(t-b) + 2b, 2(t-b) + Nb and (N+2)t are below 2^53, hence exact in double precision.
    big = (N_MAX + 2) * N_MAX
    check('all integers that enter the weights are exact in double precision', big < 2 ** 53, f'largest is below {big} < 2^53')
    t0 = time.time()
    worst, worst_N, smallest = 0.0, None, 1.0
    values = {}
    for N in range(8, N_MAX, 2):
        r, s = ratio_numpy(N)
        values[N] = r
        smallest = min(smallest, s)
        if r > worst:
            worst, worst_N = r, N
    check('no underflow: every weight, product and sum in the recursion is at least 1e-290',
          smallest >= FLOOR, f'smallest quantity {smallest:.3e}  [{time.time() - t0:.0f}s]')
    k = 6 * (N_MAX - 2) - 5                              # number of roundings that enter the bound, at N = 1686
    slack = 1.0 / (1.0 - 2.0 * k * U) - 1.0              # (1-u)^-k <= 1/(1 - k u), with room to spare
    check('rounding bound (1-u)^-(6N-5) - 1 <= 3e-12 for N <= 1686 (Lemma 3.7)', slack <= 3e-12,
          f'(6N-5) u = {k * U:.3e} at N = 1686')
    certified = worst * (1.0 + 3e-12)
    check('largest computed C_N/E_N over even 8 <= N < 1688, and the certified upper bound (Proposition 3.8)',
          certified < 0.9474 and abs(worst - 0.947) < 5e-4,
          f'computed {worst:.15f} at N = {worst_N}; certified upper bound {worst:.6f} (1 + 3e-12) < 0.9474 < 1')
    second = max(v for N, v in values.items() if N != worst_N)
    check('every computed ratio is below 0.9474, so every true ratio is below 1',
          all(v < 0.9474 for v in values.values()),
          f'{len(values)} values of N; the largest for N other than {worst_N} is {second:.6f}, and the value at N = 1686 is {values[1686]:.6f}')

    # (i) the same operations with plain Python floats
    t0 = time.time()
    sample = sorted({8, 10, 16, 50, 100, 256, 400, 1000, 1686, worst_N})
    same = all(ratio_python(N) == values[N] for N in sample)
    check('plain Python floats give the same bits as numpy', same, f'N in {sample}  [{time.time() - t0:.0f}s]')

    # (ii) exact integer arithmetic on a sample of 20 values of N
    t0 = time.time()
    sample = sorted({8, 10, 12, 16, 32, 50, 64, 100, 128, 200, 256, 400, 512, 800, 1000, 1200, 1400, 1600, 1686, worst_N})
    extra = 20
    while len(sample) < 20:                              # if the worst N was already in the list
        extra += 2
        sample = sorted(set(sample) | {extra})
    ok_sign, ok_err, max_err = True, True, 0.0
    exact_worst = None
    for N in sample:
        R = ratio_exact(N)
        ok_sign &= R < 1
        err = abs(Fraction(values[N]) / R - 1)           # exact relative error of the double-precision value
        ok_err &= err <= Fraction(3, 10 ** 12)
        max_err = max(max_err, float(err))
        if N == worst_N:
            exact_worst = R
    check(f'exact rational arithmetic for {len(sample)} values of N: C_N < E_N exactly', ok_sign, f'N in {sample}')
    check('the double-precision ratios are within the bound of Lemma 3.7 of the exact ones', ok_err,
          f'largest relative error {max_err:.2e} against the bound 3e-12  [{time.time() - t0:.0f}s]')
    small = {N: ratio_exact(N) for N in (2, 4, 6)}
    check('for N = 2, 4, 6 the hypothesis fails: C_N > E_N at eps = 2/(N+2), exactly', all(R > 1 for R in small.values()),
          ', '.join(f'N = {N}: {R.numerator}/{R.denominator}' for N, R in small.items()))
    check(f'exact value of C_N/E_N at the worst case N = {worst_N}', exact_worst < Fraction(9474, 10000),
          f'{exact_worst.numerator}/{exact_worst.denominator} = {float(exact_worst):.15f}')


# ---------------------------------------------------------------- Part 2: the Landau density near its mode

def part2():
    print('\nPart 2. The Landau density near its mode (Lemma 3.11)', flush=True)
    try:
        import flint
        from flint import acb, arb, ctx
    except ImportError:
        check('python-flint is installed', False, 'pip install python-flint')
        return
    ctx.prec = 128
    delta = arb(1) / 2 ** 20                             # 2^-20, exact
    T = arb(30)
    lam_min = arb('-0.223')                              # all lambda used below are at least -0.223

    def integrand(k, lam):
        def f(t, analytic):
            # (-t)^k exp(-t log t - lam t) sin(pi t), holomorphic off the cut of the logarithm
            return (-t) ** k * (-(t * t.log(analytic=analytic)) - lam * t).exp() * (t * acb.pi()).sin()
        return f

    def head(k):
        # On [0, delta]: |t^k e^(-t log t - lam t) sin(pi t)| <= pi t^(k+1) e^(1/e) e^(0.223 t).
        return arb.pi() * ((arb(1) / arb(1).exp()) + arb('0.223') * delta).exp() * delta ** (k + 2) / (k + 2)

    def tail(k):
        # On [T, oo): t log t + lam t >= c t with c = log T - 0.223 > 3, and for k <= 2
        # int_T^oo t^k e^(-ct) dt = e^(-cT) (T^k/c + k T^(k-1)/c^2 + k(k-1) T^(k-2)/c^3) <= T^2 e^(-cT).
        c = T.log() + lam_min
        assert c > 3 and k <= 2
        return T ** 2 * (-c * T).exp()

    def deriv(k, lam):
        """Enclosure of the k-th derivative of f_L on the ball lam (k = 1 or 2, -0.223 <= lam <= 0)."""
        assert bool(lam >= lam_min) and bool(lam <= 0) and k in (1, 2)
        I = acb.integral(integrand(k, acb(lam)), acb(delta), acb(T)).real
        err = head(k) + tail(k)
        return (I + arb(0, err.upper())) / arb.pi()

    t0 = time.time()
    ends = [float((head(k) + tail(k)).upper()) for k in (1, 2)]
    check('the 2 neglected ends [0, 2^-20] and [30, oo) are below 1e-17', max(ends) < 1e-17,
          f'python-flint {flint.__version__}, {ctx.prec} bits; at most {ends[0]:.2e} (k = 1) and {ends[1]:.2e} (k = 2)')
    a, b = arb('-0.2229'), arb('-0.2227')
    fa, fb = deriv(1, a), deriv(1, b)
    check("f_L'(-0.2229) > 0 > f_L'(-0.2227)", bool(fa > 0) and bool(fb < 0), f'enclosures {fa.str(12)} and {fb.str(12)}')
    check("f_L'(-0.2229) in [9.232e-6, 9.234e-6] and f_L'(-0.2227) in [-6.548e-6, -6.546e-6] (as printed in the paper)",
          bool(fa > arb('9.232e-6')) and bool(fa < arb('9.234e-6')) and bool(fb > arb('-6.548e-6')) and bool(fb < arb('-6.546e-6')),
          'both enclosures lie inside the printed intervals')
    box = a.union(b)
    f2 = deriv(2, box)
    check("f_L'' in [-0.0792, -0.0786] on [-0.2229, -0.2227], hence below -0.078 (as printed in the paper)",
          bool(f2 < arb('-0.0786')) and bool(f2 > arb('-0.0792')),
          f'enclosure [{float(f2.lower()):.6f}, {float(f2.upper()):.6f}]')
    # Sharper enclosures, for the record (the paper prints lambda_0 = -0.2228 and f_L''(lambda_0) = -0.0789).
    a1, b1 = arb('-0.22278299'), arb('-0.22278297')
    fa1, fb1 = deriv(1, a1), deriv(1, b1)
    check('the mode lies in (-0.22278299, -0.22278297)', bool(fa1 > 0) and bool(fb1 < 0),
          f"f_L' there: {fa1.str(8)} and {fb1.str(8)}")
    f2s = deriv(2, a1.union(b1))
    check("f_L''(lambda_0) = -0.0789 to 4 decimals", bool(f2s < arb('-0.07885')) and bool(f2s > arb('-0.07895')),
          f'enclosure {f2s.str(10)}  [{time.time() - t0:.1f}s]')


def main():
    T0 = time.time()
    print('Paper D: certified computations for the elephant walk')
    part1()
    part2()
    print(f'\nCertification done in {time.time() - T0:.0f}s: '
          + ('all passed.' if not FAILS else f'{len(FAILS)} FAILED: ' + '; '.join(FAILS)))
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
