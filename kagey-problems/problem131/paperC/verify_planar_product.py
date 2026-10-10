"""Paper C, Section 6: the product curve (Proposition prop:product) and turns only (Theorem thm:pureturns).

Check 1 is the product identity in exact rational arithmetic, for N = 4, 6, 8 with one rho each.
The other checks are in floating point and only on grids.
Check 2 (turns only, N = 8, 16, 32, 64, 96, at x = u_N/2, u_N, 3u_N/2): Delta_N >= 0 and the bound
of Theorem 6.9(b) where z(z+2) <= N. Here Delta_N is computed as S_N^2 - o_N/c_N, so this check
does not test the identity of Theorem 6.9(a). verify_planar.py tests that identity exactly.
Check 3: F(y/2) <= 2 F(y) of Appendix C, at 4000 points y from 1e-3 to 1e4.
Check 4: x S_N'(x) <= (2z+2) S_N(x) of Lemma C.4, for N = 16, 64, 256 at 30 values of z with
z(z+2) <= N, with the derivative taken as a central difference.
Every check asserts, so a failure stops the script with an error. The size of N v*_N - N u_N
against L^2/N (Theorem 6.9(c)) is only printed, because the theorem gives no constant.
Accepts and ignores --full.
"""
import itertools
import math
from fractions import Fraction

import numpy as np

DIRS = [(1, 0), (0, 1), (-1, 0), (0, -1)]


def planar_law(N, keep, turn, rev, exact=False):
    """Law of the position after N steps. First direction uniform."""
    zero = Fraction(0) if exact else 0.0
    quarter = Fraction(1, 4) if exact else 0.25
    cur = {}
    for d in range(4):
        cur[(DIRS[d][0], DIRS[d][1], d)] = quarter
    for _ in range(N - 1):
        nxt = {}
        for (x, y, d), p in cur.items():
            for dd, w in ((d, keep), ((d + 1) % 4, turn), ((d + 3) % 4, turn), ((d + 2) % 4, rev)):
                if w == 0:
                    continue
                key = (x + DIRS[dd][0], y + DIRS[dd][1], dd)
                nxt[key] = nxt.get(key, zero) + p * w
        cur = nxt
    law = {}
    for (x, y, d), p in cur.items():
        law[(x, y)] = law.get((x, y), zero) + p
    return law


def kagey_law(N, rho, exact=False):
    """Law of the number of right steps of Paper A's walk with switch probability rho."""
    zero = Fraction(0) if exact else 0.0
    half = Fraction(1, 2) if exact else 0.5
    cur = {(1, 1): half, (0, 0): half}  # (rights, last is right)
    for _ in range(N - 1):
        nxt = {}
        for (k, last), p in cur.items():
            for nl, w in ((last, 1 - rho), (1 - last, rho)):
                key = (k + nl, nl)
                nxt[key] = nxt.get(key, zero) + p * w
        cur = nxt
    law = {}
    for (k, last), p in cur.items():
        law[k] = law.get(k, zero) + p
    return law


print("1. product identity, exact rational arithmetic")
for N, rho in ((4, Fraction(1, 3)), (6, Fraction(2, 7)), (8, Fraction(1, 5))):
    pl = planar_law(N, (1 - rho) ** 2, rho * (1 - rho), rho ** 2, exact=True)
    ka = kagey_law(N, rho, exact=True)
    ok = True
    for (x, y), p in pl.items():
        ku, kv = (N + x + y) // 2, (N + x - y) // 2
        if p != ka[ku] * ka[kv]:
            ok = False
    print("   N=%d rho=%s: every bin equals the product: %s  (o/c = %s, S_N^2 = %s)" % (
        N, rho, ok, pl[(0, 0)] / pl[(N, 0)], (ka[N // 2] / ka[N]) ** 2))
    assert ok, "product identity fails at N=%d" % N


def S_N(N, x):
    """S_N(x) = P_N(N/2)/P_N(0) for Paper A's walk with odds x of a switch, by a stable recursion."""
    # weights: word weight x^{switches}; W[k][last]
    W = np.zeros((N + 1, 2))
    W[1, 1] = 1.0
    W[0, 0] = 1.0
    for _ in range(N - 1):
        V = np.zeros_like(W)
        V[1:, 1] = W[:-1, 1] + x * W[:-1, 0]
        V[:, 0] = W[:, 0] + x * W[:, 1]
        W = V
    return W[N // 2].sum()


def planar_ratio_turns(N, v):
    """o_N / c_N for turns only, with odds v of a turn to a given side: weights v^{turns}."""
    cur = {}
    for d in range(4):
        cur[(DIRS[d][0], DIRS[d][1], d)] = 1.0
    for _ in range(N - 1):
        nxt = {}
        for (x, y, d), p in cur.items():
            for dd, w in ((d, 1.0), ((d + 1) % 4, v), ((d + 3) % 4, v)):
                key = (x + DIRS[dd][0], y + DIRS[dd][1], dd)
                nxt[key] = nxt.get(key, 0.0) + p * w
        cur = nxt
    return sum(p for (x, y, d), p in cur.items() if x == 0 and y == 0)


def root(f, lo, hi, it=200):
    for _ in range(it):
        mid = 0.5 * (lo + hi)
        if f(mid) < 1:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


print("2. turns only: S_N(v)^2 - o/c >= 0, the bound of Theorem 6.9(b), and the crossing")
for N in (8, 16, 32, 64, 96):
    uN = root(lambda x: S_N(N, x), 0.0, 1.0)
    vstar = root(lambda x: planar_ratio_turns(N, x), 0.0, 1.0)
    L = math.log(N)
    worst, tested = 0.0, 0
    for x in (0.5 * uN, uN, 1.5 * uN):
        z = N * x
        S = S_N(N, x)
        Delta = S * S - planar_ratio_turns(N, x)
        assert Delta >= -1e-12
        if z * (z + 2) <= N:          # the hypothesis of Theorem 6.9(b)
            bound = (2 * x + 8 * x * S) * (2 * z + 2) * S
            assert Delta <= bound * (1 + 1e-9)
            worst = max(worst, Delta / bound)
            tested += 1
    print("   N=%3d  N*u_N=%.5f  N*v*=%.5f  N(v*-u_N)*N/L^2=%.4f  max Delta/bound=%.4f"
          "  (bound tested at %d of 3 points, the others have z(z+2) > N)" % (
        N, N * uN, N * vstar, N * (vstar - uN) * N / L ** 2, worst, tested))

print("3. F(y/2) <= 2 F(y) for F(y) = exp(-y)(I0+I1)(y)")
from scipy.special import ive
ys = np.geomspace(1e-3, 1e4, 4000)
F = lambda y: ive(0, y) + ive(1, y)
supF = np.max(F(ys / 2) / F(ys))
print("   sup F(y/2)/F(y) on the grid: %.6f" % supF)
assert supF <= 2 * (1 + 1e-9)

print("4. x S_N'(x) <= (2z+2) S_N(x) when z(z+2)/(2N) <= 1/2 (Lemma C.4)")
for N in (16, 64, 256):
    worst = 0.0
    for z in np.linspace(0.2, min(math.sqrt(N) - 1.0, 12), 30):   # z <= sqrt(N) - 1 gives z(z+2) <= N
        x = z / N
        d = 1e-6
        deriv = (S_N(N, x * (1 + d)) - S_N(N, x * (1 - d))) / (2 * d)
        worst = max(worst, deriv / ((2 * z + 2) * S_N(N, x)))
    print("   N=%3d  max xS'/((2z+2)S) = %.4f" % (N, worst))
    assert worst <= 1 + 1e-6     # the derivative is a central difference, hence the tolerance
