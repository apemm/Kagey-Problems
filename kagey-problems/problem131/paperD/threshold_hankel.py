"""Certify from even moments that the fair-start law is not symmetric unimodal.

Helper of certify_threshold.py (Lemma lem:thr-hankel, Theorem thm:threshold).
If L is symmetric and unimodal, Khinchine's theorem gives L = U Z with U uniform
on (0,1) independent of Z, so s_j = (2j+1) E[L^(2j)] = E[(Z^2)^j] is a Stieltjes
moment sequence and both Hankel matrices H0 = (s_(i+j)) and H1 = (s_(i+j+1)),
0 <= i,j <= k, are positive semidefinite. Here E[L^(2j)] = (2j)! m_(2j) / Gamma(1+2ja)
(moment recursion of Guerin, Laulin and Raschel, Theorem 1.4).

For each box [lo, hi] of a the script picks an order k and a rational test
vector x (from a float eigenvector at the box centre, a choice that is not part
of the proof) and checks that Q(a) = x^T H x < 0 for all a in the box, H = H0 or
H1. Q is analytic in a, and the check uses a Taylor model of Q at the box
centre: coefficients from arb_series arithmetic at the exact centre, and a
Cauchy remainder from acb enclosures of the moments on a complex square around
the box (Lemma lem:thr-taylor). Boxes that fail are bisected.
"""
import time
from fractions import Fraction

import mpmath
from flint import acb, arb, arb_series, ctx, fmpq

from threshold_pointwise import require
from threshold_taylor import sign_cover

ORDERS = [1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 40, 48, 56, 64]


def moments_mp(a, nmax):
    m = [mpmath.mpf(1), mpmath.mpf(1)]
    for n in range(2, nmax + 1):
        s = sum((a if j % 2 else 1) * m[j] * m[n - j] for j in range(1, n))
        m.append(s / (n * a - (a if n % 2 else 1)))
    return [mpmath.factorial(n) * m[n] / mpmath.gamma(1 + a * n) for n in range(nmax + 1)]


def hankels_mp(a, k):
    M = moments_mp(a, 4 * k + 2)
    s = [(2 * j + 1) * M[2 * j] for j in range(2 * k + 2)]
    H0 = mpmath.matrix(k + 1, k + 1)
    H1 = mpmath.matrix(k + 1, k + 1)
    for i in range(k + 1):
        for j in range(k + 1):
            H0[i, j] = s[i + j]
            H1[i, j] = s[i + j + 1]
    return H0, H1


def test_vector(a, k):
    """Return (shift, x) with x^T H_shift x < 0 at a (floats only), or None."""
    best = None
    for sh, H in enumerate(hankels_mp(mpmath.mpf(a.numerator) / a.denominator, k)):
        # scale to unit diagonal for conditioning
        d = [mpmath.sqrt(H[i, i]) for i in range(k + 1)]
        Hs = mpmath.matrix(k + 1, k + 1)
        for i in range(k + 1):
            for j in range(k + 1):
                Hs[i, j] = H[i, j] / (d[i] * d[j])
        E, Q = mpmath.eigsy(Hs)
        i0 = min(range(k + 1), key=lambda i: E[i])
        if E[i0] < 0 and (best is None or E[i0] < best[0]):
            x = [Q[i, i0] / d[i] for i in range(k + 1)]
            mx = max(abs(v) for v in x)
            x = [Fraction(mpmath.nstr(v / mx, 40)) for v in x]
            best = (E[i0], sh, x)
    return None if best is None else best[1:]


def check_box_tm(lo, hi, k, sh, x, q=Fraction(1, 8)):
    """Return (ok, Q0, rem): Taylor-model check that Q < 0 on [lo, hi]."""
    a0 = (lo + hi) / 2
    w = (hi - lo) / 2
    rho = min(w / q, (a0 - Fraction(1, 2)) * Fraction(9, 10))
    qq = w / rho
    # the Cauchy remainder M qq^(K+1)/(1-qq) is valid only for qq < 1
    require(qq < 1, "box too wide for its distance to 1/2")
    nmax = 4 * k + 2
    a0b = arb(fmpq(a0.numerator, a0.denominator))
    rb = arb(fmpq(rho.numerator, rho.denominator))
    S = acb(a0b + arb(0, rb), arb(0, rb))
    m = [acb(1), acb(1)]
    for n in range(2, nmax + 1):
        t = acb(0)
        for j in range(1, n):
            t += (S if j % 2 else 1) * m[j] * m[n - j]
        m.append(t / (n * S - (S if n % 2 else 1)))
    ES = [arb.fac_ui(n) * m[n] * (1 + n * S).rgamma() for n in range(nmax + 1)]
    sS = [((2 * j + 1) * ES[2 * j]).abs_upper() for j in range(2 * k + 2)]
    xb = [arb(fmpq(v.numerator, v.denominator)) for v in x]
    M = arb(0)
    for i in range(k + 1):
        for j in range(k + 1):
            M += abs(xb[i] * xb[j]) * sS[i + j + sh]
    qb = arb(fmpq(qq.numerator, qq.denominator))
    lm = float(M.log().upper())
    K = max(4, int((lm + 60) / -float(qb.log().mid())) + 2)
    rem = (M * qb ** (K + 1) / (1 - qb)).upper()
    ctx.cap = K + 1
    eps = arb_series([arb(0), arb(1)])
    z = a0b + eps
    one = arb_series([arb(1)])
    ms = [one, one]
    for n in range(2, nmax + 1):
        t = arb_series([arb(0)])
        for j in range(1, n):
            t += (z * (ms[j] * ms[n - j])) if j % 2 else ms[j] * ms[n - j]
        ms.append(t / (n * z - (z if n % 2 else 1)))
    sser = [(2 * j + 1) * arb.fac_ui(2 * j) * ms[2 * j] * (1 + 2 * j * z).rgamma()
            for j in range(2 * k + 2)]
    Qs = arb_series([arb(0)])
    for i in range(k + 1):
        for j in range(k + 1):
            Qs += xb[i] * xb[j] * sser[i + j + sh]
    Qc = Qs.coeffs() + [arb(0)] * (K + 1)
    Qc = Qc[:K + 1]
    cover = sign_cover(Qc, rem, a0, w, max_depth=30)
    ok = all(sg == -1 for (_, _, sg) in cover)
    return ok, Qc[0], rem


def certify(lo, hi, depth=0, log=None):
    mid = (lo + hi) / 2
    for k in ORDERS:
        mpmath.mp.dps = 60 + 6 * k
        tv = test_vector(mid, k)
        if tv is None:
            continue
        sh, x = tv
        ok, q0, rem = check_box_tm(lo, hi, k, sh, x)
        if ok:
            log.append((lo, hi, k, sh, q0, rem))
            print("a in [%.12f, %.12f]  k=%2d  H%d  Q(centre) = %s  remainder <= %s"
                  % (lo, hi, k, sh, q0.str(5), rem.str(3)), flush=True)
            return True
        break
    if depth > 40:
        return False
    return certify(lo, mid, depth + 1, log) and certify(mid, hi, depth + 1, log)


def run(a_lo, a_hi=Fraction(1)):
    """Cover [a_lo, a_hi] by certified boxes. Returns True on success."""
    ctx.prec = 1500
    t0 = time.time()
    # coarse initial boxes, finer near a_lo
    edges = [a_lo]
    x = a_lo
    while x < a_hi:
        step = max(Fraction(1, 1000), (x - Fraction(2, 3)) / 4)
        x = min(a_hi, x + step)
        edges.append(x)
    log = []
    ok = True
    for lo, hi in zip(edges, edges[1:]):
        ok &= certify(lo, hi, 0, log)
    print("boxes: %d  covered [%s, %s]: %s" % (len(log), a_lo, a_hi, "yes" if ok else "NO"))
    print("elapsed %.1f s" % (time.time() - t0))
    return ok
