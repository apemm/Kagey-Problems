"""Checks for Proposition 3.26 (odd N) and the numbers of Remark 3.28.

 1. The identity  P_N((N+1)/2) = C_{N+1} / (1 - (1-2 eps)/N)  for odd N, in exact rational
    arithmetic for small N and in double precision for larger N.
 2. The crossing x_N for odd N against the root g_N of g + log g = 2 log N - log 8.
    The scaled difference (x_N - g_N) N / (log N)^2 has the size that it has for even N.
 3. The constants in the proof of part (c): at eps = 2/N and odd N >= 1689 the bound for the
    two central bins is below 1.4e-3 and the end is above 0.06.
 4. In double precision, the two central bins are below the end at eps = 2/N for odd
    1689 <= N <= 1699, and x_N > 2 for a sample of odd N.
 5. The Landau density (numerical, not certified): its right half-maximum point 2.432 and its
    right inflection point 1.104, with the thresholds 252.8 and 4.8 for x quoted in the remark.
Run: python -B verify_elephant_odd.py     (about 10 seconds)
"""
import math
import sys
from fractions import Fraction

import mpmath as mp
import numpy as np
from scipy.optimize import brentq

FAILS = []


def check(label, ok, detail=''):
    print(('  ok    ' if ok else '  FAIL  ') + label + (': ' + detail if detail else ''), flush=True)
    if not ok:
        FAILS.append(label)


def law_exact(N, eps):
    """P(A_N = a) for a = 0..N with a fair first step, in exact arithmetic."""
    c = 1 - 2 * eps
    P = [Fraction(1, 2), Fraction(1, 2)]
    for t in range(1, N):
        Q = [Fraction(0)] * (t + 2)
        for a in range(t + 1):
            r = eps + c * a / t
            Q[a] += P[a] * (1 - r)
            Q[a + 1] += P[a] * r
        P = Q
    return P


def law(N, eps):
    c = 1 - 2 * eps
    P = np.zeros(N + 2)
    P[0] = P[1] = 0.5
    a = np.arange(N + 2)
    for t in range(1, N):
        r = eps + c * a / t
        Q = P * (1 - r)
        Q[1:] += (P * r)[:-1]
        P = Q
    return P[:N + 1]


def center(P, N):
    return P[N // 2] if N % 2 == 0 else P[(N + 1) // 2]


def g_root(N):
    lam = 2 * math.log(N) - math.log(8)
    return brentq(lambda x: x + math.log(x) - lam, 1e-3, 100)


def crossing(N):
    def F(x):
        P = law(N, x / N)
        return math.log(center(P, N)) - math.log(P[N])
    g = g_root(N)
    return brentq(F, 0.3 * g, g + 1.0, xtol=1e-12)


def main():
    print('1. the identity for the two central bins')
    worst = Fraction(0)
    for N in (3, 5, 7, 9, 15, 21):
        for eps in (Fraction(1, 50), Fraction(1, 7), Fraction(2, 5), Fraction(3, 4)):
            PN, PN1 = law_exact(N, eps), law_exact(N + 1, eps)
            k = (N + 1) // 2
            worst = max(worst, abs(PN[k] * (1 - (1 - 2 * eps) / N) - PN1[k]), abs(PN[k] - PN[k - 1]))
    check('exact for N = 3, 5, 7, 9, 15, 21 and four rational eps', worst == 0)
    worst = 0.0
    for N in (51, 201, 1001, 3001):
        for eps in (0.002, 0.02, 0.3):
            PN, PN1 = law(N, eps), law(N + 1, eps)
            k = (N + 1) // 2
            worst = max(worst, abs(PN[k] * (1 - (1 - 2 * eps) / N) / PN1[k] - 1))
    check('double precision for N = 51, 201, 1001, 3001', worst < 1e-12, 'relative error %.1e' % worst)

    print('2. the crossing for odd N')
    scaled = []
    for N in (201, 401, 801, 1601, 3201):
        x, g = crossing(N), g_root(N)
        xe = crossing(N - 1)
        scaled.append((x - g) * N / math.log(N) ** 2)
        print('        N = %d: x_N = %.6f, g_N = %.6f, x_(N-1) = %.6f' % (N, x, g, xe))
        check('x_N lies between g_N - 1 and g_N, and within 0.01 of x_(N-1), at N = %d' % N,
              g - 1 < x < g and abs(x - xe) < 0.01)
        check('x_N > 2 at N = %d' % N, x > 2)
    check('(x_N - g_N) N / (log N)^2 is below 5 in absolute value, as for even N', max(abs(s) for s in scaled) < 5,
          ', '.join('%.2f' % s for s in scaled))

    print('3. the constants in the proof of part (c)')
    def bound(N):
        return 8 / (N * (N + 3)) * (N + 1) ** (4 / N) * math.exp(10400 / N) * N / (N - 1)
    check('eps (1 + log(N+1)) <= 1/100 at eps = 2/N, N = 1689', 2 / 1689 * (1 + math.log(1690)) <= 0.01,
          '%.6f' % (2 / 1689 * (1 + math.log(1690))))
    check('the bound for the two central bins is below 1.4e-3 at N = 1689', bound(1689) < 1.4e-3, '%.4e' % bound(1689))
    check('the bound decreases in N (odd N from 1689 to 10^5)',
          all(bound(N + 2) < bound(N) for N in range(1689, 100001, 2)))
    check('the end is above 0.06', 0.5 * math.exp(-2 - 2 / 1689) > 0.06, '%.4f' % (0.5 * math.exp(-2 - 2 / 1689)))

    print('4. the two central bins against the end at eps = 2/N')
    ratios = []
    for N in range(1689, 1700, 2):
        P = law(N, 2.0 / N)
        ratios.append(center(P, N) / P[N])
    check('central bins below the end for odd 1689 <= N <= 1699', max(ratios) < 1, 'largest ratio %.2e' % max(ratios))

    print('5. the Landau density (numerical)')
    mp.mp.dps = 20

    def fL(lam, d=0):
        g = lambda s: mp.e ** (-s * mp.log(s) - lam * s) * mp.sin(mp.pi * s) * (-s) ** d if s > 0 else mp.mpf(0)
        return mp.quad(g, mp.linspace(0, 40, 81)) / mp.pi

    l0 = mp.findroot(lambda l: fL(l, 1), -0.22)
    lh = mp.findroot(lambda l: fL(l) - fL(l0) / 2, 3.0)
    l1 = mp.findroot(lambda l: fL(l, 2), 1.0)
    check('mode of f_L', abs(l0 + 0.222783) < 1e-6, mp.nstr(l0, 8))
    check('right half-maximum point 2.432', abs(lh - 2.432) < 5e-4, mp.nstr(lh, 6))
    check('right inflection point 1.104', abs(l1 - 1.104) < 5e-4, mp.nstr(l1, 6))
    xs = mp.e ** (2 * lh - 3 * l0)
    logN = (xs + mp.log(xs) + mp.log(8)) / 2          # from x + log x = 2 log N - log 8
    check('Step 3 needs x above 252.8, which is N above about 3e56', 252.7 < xs < 252.9 and 3e56 < mp.e ** logN < 4e56,
          'x = %s, N = %s' % (mp.nstr(xs, 5), mp.nstr(mp.e ** logN, 3)))
    check('the inflection is below twice the mode once x >= 4.8', 4.7 < mp.e ** (l1 - 2 * l0) < 4.8,
          mp.nstr(mp.e ** (l1 - 2 * l0), 5))

    print('\nOdd N checks: ' + ('all passed.' if not FAILS else '%d FAILED: ' % len(FAILS) + '; '.join(FAILS)))
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
