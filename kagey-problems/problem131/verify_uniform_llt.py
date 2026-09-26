"""Uniform local limit theorem for the binary persistent walk (Problem 131, Paper A).

Standard library only (fractions, decimal, math, json).

Checks, for P_N(k) = probability of k right steps in N steps:
  (E)  the exact identity P_N(k) = (q/2)[2P(D=0)+P(D=1)+P(D=-1)], D = Bin(k-1,q) - Bin(N-k-1,q);
  (U)  the tilted Bessel (Skellam) approximation
         U = (q/2) Lambda(s) e^{-x} [2 I_0(x) + (s+1/s) I_1(x)],  x = sigma^2 at the saddle s;
  (G)  the same with e^{-x} I_j(x) replaced by 1/sqrt(2 pi x);
  (TM) the transfer-matrix Gaussian saddle point;
  (B)  the Bessel form of Paper A, Theorem thm:allbin-bessel;
and the explicit error bound of the uniform local law (Theorem thm:llt).

Usage:  python verify_uniform_llt.py          run 1 (identity, U/G/TM/B errors over all bins)
        python verify_uniform_llt.py --run2   run 2 (proof-consistency checks, N = 10^4, q > 1/2)
        python verify_uniform_llt.py --run3   run 3 (the centre crossing from U against Paper A)

Every exact probability is computed twice (recursion eq:dp and the run-count formula), every
scaled Bessel value twice (Decimal power series and the trapezoid rule for DLMF 10.32.3), and the
saddle twice (closed form and bisection).  Outputs go to data/uniform-llt-verification.json and
data/uniform-llt-verification.txt.
"""
from fractions import Fraction
from decimal import Decimal, getcontext
import math
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "data")
getcontext().prec = 60


# ---------------------------------------------------------------- exact probabilities

def dp_row(N, q):
    """Row P_N(0..N) from the recursion eq:dp.  Works with float or Fraction q."""
    p = 1 - q
    half = Fraction(1, 2) if isinstance(q, Fraction) else 0.5
    zero = q * 0
    R = [zero, half]      # R_1(k), k = 0, 1
    L = [half, zero]
    for n in range(2, N + 1):
        R2 = [zero] * (n + 1)
        L2 = [zero] * (n + 1)
        for k in range(1, n + 1):          # R_n(k) = p R_{n-1}(k-1) + q L_{n-1}(k-1)
            R2[k] = p * R[k - 1] + q * L[k - 1]
        for k in range(0, n):              # L_n(k) = p L_{n-1}(k) + q R_{n-1}(k)
            L2[k] = p * L[k] + q * R[k]
        R, L = R2, L2
    return [R[k] + L[k] for k in range(N + 1)]


def runcount_exact(N, k, q):
    """Theorem thm:pmf with math.comb and Fractions (exact)."""
    p = 1 - q
    if k in (0, N):
        return Fraction(1, 2) * p ** (N - 1)
    a, b = k, N - k
    tot = 0
    for j in range(1, N):
        if j % 2 == 1:
            i = (j + 1) // 2
            W = 2 * math.comb(a - 1, i - 1) * math.comb(b - 1, i - 1)
        else:
            i = j // 2
            W = math.comb(a - 1, i) * math.comb(b - 1, i - 1) + math.comb(a - 1, i - 1) * math.comb(b - 1, i)
        if W:
            tot += W * p ** (N - 1 - j) * q ** j
    return Fraction(1, 2) * tot


def lcomb(n, r):
    return math.lgamma(n + 1) - math.lgamma(r + 1) - math.lgamma(n - r + 1)


def runcount_log(N, k, q):
    """Theorem thm:pmf in log space (float).  Returns log P_N(k)."""
    p = 1.0 - q
    lp, lq = math.log(p), math.log(q)
    if k in (0, N):
        return math.log(0.5) + (N - 1) * lp
    a, b = k, N - k
    terms = []
    for i in range(1, min(a, b) + 1):          # odd j = 2i-1
        j = 2 * i - 1
        terms.append(math.log(2) + lcomb(a - 1, i - 1) + lcomb(b - 1, i - 1) + (N - 1 - j) * lp + j * lq)
    for i in range(1, min(a, b) + 1):          # even j = 2i (terms vanish for i > min(a,b))
        j = 2 * i
        if j > N - 1:
            break
        parts = []
        if i <= a - 1 and i - 1 <= b - 1:
            parts.append(lcomb(a - 1, i) + lcomb(b - 1, i - 1))
        if i - 1 <= a - 1 and i <= b - 1:
            parts.append(lcomb(a - 1, i - 1) + lcomb(b - 1, i))
        for t in parts:
            terms.append(t + (N - 1 - j) * lp + j * lq)
    m = max(terms)
    return math.log(0.5) + m + math.log(sum(math.exp(t - m) for t in terms))


def identity_rhs_exact(N, k, q):
    """(q/2)[2P(D=0)+P(D=1)+P(D=-1)] with D = Bin(k-1,q) - Bin(N-k-1,q), exact."""
    p = 1 - q
    n1, n2 = k - 1, N - k - 1
    B1 = [math.comb(n1, r) * q ** r * p ** (n1 - r) for r in range(n1 + 1)]
    B2 = [math.comb(n2, r) * q ** r * p ** (n2 - r) for r in range(n2 + 1)]

    def PD(j):
        return sum(B1[r] * B2[r - j] for r in range(n1 + 1) if 0 <= r - j <= n2)
    return Fraction(q, 1) / 2 * (2 * PD(0) + PD(1) + PD(-1)) if isinstance(q, Fraction) else None


# ---------------------------------------------------------------- scaled Bessel e^{-x} I_j(x)

def besse_series(j, x):
    """e^{-x} I_j(x) by the power series (DLMF 10.25.2) in 60-digit Decimal."""
    X = Decimal(repr(x))
    h = X / 2
    term = h ** j / Decimal(math.factorial(j))
    s = term
    m = 0
    while True:
        m += 1
        term = term * h * h / (Decimal(m) * Decimal(m + j))
        s += term
        if term < s * Decimal(10) ** -40 and m > x:
            break
    return float(s * (-X).exp())


def besse_trap(j, x, M=6000):
    """e^{-x} I_j(x) = (1/pi) int_0^pi e^{x(cos t-1)} cos(jt) dt (DLMF 10.32.3), trapezoid rule."""
    h = math.pi / M
    s = 0.5 * (1.0 + math.exp(-2 * x) * math.cos(j * math.pi))
    for i in range(1, M):
        t = i * h
        s += math.exp(x * (math.cos(t) - 1.0)) * math.cos(j * t)
    return s * h / math.pi


# ---------------------------------------------------------------- saddle point of the D-tilt

def saddle_closed(n1, n2, q):
    p = 1.0 - q
    A = n1 * p
    Bc = (n1 - n2) * q
    C = -n2 * p
    disc = Bc * Bc - 4 * A * C
    # stable root of A s^2 + B s + C = 0, the positive one
    if Bc >= 0:
        return (2 * -C) / (Bc + math.sqrt(disc))
    return (-Bc + math.sqrt(disc)) / (2 * A)


def saddle_bisect(n1, n2, q):
    p = 1.0 - q

    def f(ls):
        s = math.exp(ls)
        return n1 * q * s / (p + q * s) - n2 * q / (p * s + q)
    lo, hi = -60.0, 60.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if f(mid) > 0:
            hi = mid
        else:
            lo = mid
    return math.exp(0.5 * (lo + hi))


def tilt_quantities(n1, n2, q, s):
    p = 1.0 - q
    pi1 = q * s / (p + q * s)
    pi2 = q / (p * s + q)
    v1, v2 = pi1 * (1 - pi1), pi2 * (1 - pi2)
    x = n1 * v1 + n2 * v2
    logLam = n1 * math.log(p + q * s) + n2 * math.log(p + q / s)
    return pi1, pi2, v1, v2, x, logLam


def approx_U(N, k, q, bessel=besse_series, saddle=saddle_closed):
    n1, n2 = k - 1, N - k - 1
    s = saddle(n1, n2, q)
    pi1, pi2, v1, v2, x, logLam = tilt_quantities(n1, n2, q, s)
    K0, K1 = bessel(0, x), bessel(1, x)
    return math.log(q / 2) + logLam + math.log(2 * K0 + (s + 1 / s) * K1)


def approx_G(N, k, q):
    n1, n2 = k - 1, N - k - 1
    s = saddle_closed(n1, n2, q)
    pi1, pi2, v1, v2, x, logLam = tilt_quantities(n1, n2, q, s)
    return math.log(q / 2) + logLam + math.log(2 + s + 1 / s) - 0.5 * math.log(2 * math.pi * x)


def approx_TM(N, k, q):
    """Transfer-matrix Gaussian saddle point for X_N = 2k - N (span 2)."""
    p = 1.0 - q
    xg = 2 * k - N

    def parts(t):
        sh, ch = math.sinh(t), math.cosh(t)
        S = math.sqrt(q * q + p * p * sh * sh)
        lp_ = p * ch + S
        lm_ = p * ch - S
        d1 = p * sh + p * p * sh * ch / S
        d2 = p * ch + p * p * (ch * ch + sh * sh) / S - p ** 4 * sh * sh * ch * ch / S ** 3
        k1 = d1 / lp_
        k2 = d2 / lp_ - k1 * k1
        return lp_, lm_, k1, k2

    lo, hi = -50.0, 50.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if (N - 1) * parts(mid)[2] > xg:
            hi = mid
        else:
            lo = mid
    t = 0.5 * (lo + hi)
    lp_, lm_, k1, k2 = parts(t)
    phi1 = math.cosh(t)
    phi2 = p * math.cosh(2 * t) + q
    cplus = (phi2 - lm_ * phi1) / (lp_ - lm_)
    return math.log(2 * cplus) + (N - 1) * math.log(lp_) - t * xg - 0.5 * math.log(2 * math.pi * (N - 1) * k2)


def approx_B(N, k, q):
    """Paper A: (1/2) p^{N-1} T_{a,b}(u) = p^{N-1} u [I_0(2su) + c I_1(2su)], s = sqrt(ab)."""
    p = 1.0 - q
    a, b = k, N - k
    u = q / p
    sab = math.sqrt(a * b)
    c = (a + b) / (2 * sab)
    y = 2 * sab * u
    val = besse_series(0, y) + c * besse_series(1, y)       # times e^{y}
    return (N - 1) * math.log(p) + math.log(u) + y + math.log(val)


# ---------------------------------------------------------------- the explicit bound (Theorem LLT)

def rho(x):
    return besse_series(1, x) / besse_series(0, x) if x > 0 else 0.0


def tilt_all(N, k, q):
    n1, n2 = k - 1, N - k - 1
    s = saddle_closed(n1, n2, q)
    pi1, pi2, v1, v2, x, logLam = tilt_quantities(n1, n2, q, s)
    m = n1 * pi1
    V = n1 * v1 * v1 + n2 * v2 * v2
    M = m * max(pi1, pi2)
    return n1, n2, s, pi1, pi2, v1, v2, x, logLam, m, V, M


def kappa_moments(x):
    """rho, <kappa^2>, <kappa^3> for the density proportional to e^{x(cos t-1)} on [-pi, pi]."""
    r = rho(x)
    return r, 2 - 2 * r - r / x, 4 - 4 * r - 3 * r / x - 2 * r / x ** 2 + 1 / x


def theorem_bound(N, k, q):
    """E = (1/rho)[(4V + (64/3)M)<kappa^2> + (1024/9) M^2 <kappa^3>]  (Theorem thm:llt)."""
    n1, n2, s, pi1, pi2, v1, v2, x, logLam, m, V, M = tilt_all(N, k, q)
    r, k2, k3 = kappa_moments(x)
    return ((4 * V + 64.0 / 3 * M) * k2 + 1024.0 / 9 * M * M * k3) / r


def argA(pi, t):
    """A(pi, t) = arg(1 - pi + pi e^{it}), continuous on (-pi, pi)."""
    return math.atan2(pi * math.sin(t), 1 - pi + pi * math.cos(t))


def intermediate_bound(N, k, q, Mq=4000):
    """E_int = (1/rho)[<min(1,4 kappa^2 V)> + <Phi^2>/2 + <|Phi||sin t|>] by the midpoint rule,
    and the Fourier representation of P_N(k) (a third evaluation of P_N(k)).
    Returns (E_int, log P_N(k) from the Fourier integral,
             max over t of (g-|psi|)/(g min(1,4 kappa^2 V)))."""
    n1, n2, s, pi1, pi2, v1, v2, x, logLam, m, V, M = tilt_all(N, k, q)
    h = math.pi / Mq
    Z = A1 = A2 = A3 = 0.0
    rep = 0.0
    worst_mod = 0.0
    for i in range(Mq):
        t = (i + 0.5) * h
        kap = 1 - math.cos(t)
        g = math.exp(-x * kap)
        lpsi = 0.5 * n1 * math.log(1 - 2 * v1 * kap) + 0.5 * n2 * math.log(1 - 2 * v2 * kap)
        apsi = math.exp(lpsi)
        Phi = n1 * argA(pi1, t) - n2 * argA(pi2, t)
        mm = min(1.0, 4 * kap * kap * V)
        if mm > 0:
            # 1 - |psi|/g = 1 - exp(-sum n_j ell(z_j)), ell(z) = -(log(1-z) + z)/2, computed without
            # cancellation (run 2 first used (g - |psi|)/g directly, which cancels when both are near 1)
            def ell(z):
                return -(math.log1p(-z) + z) / 2 if z > 1e-4 else z * z / 4 + z ** 3 / 6 + z ** 4 / 8
            deficit = -math.expm1(-(n1 * ell(2 * v1 * kap) + n2 * ell(2 * v2 * kap)))
            worst_mod = max(worst_mod, deficit / mm)
        Z += g
        A1 += g * mm
        A2 += g * Phi * Phi
        A3 += g * abs(Phi) * math.sin(t)
        rep += apsi * (math.cos(Phi) * (2 + (s + 1 / s) * math.cos(t))
                       - math.sin(Phi) * (s - 1 / s) * math.sin(t))
    Eint = (A1 / Z + 0.5 * A2 / Z + A3 / Z) / rho(x)
    logP_fourier = math.log(q / 2) + logLam + math.log(rep * h / math.pi)
    return Eint, logP_fourier, worst_mod


def dp_low_bins(N, q, K):
    """log P_N(k) for k <= K by the recursion eq:dp restricted to k <= K, in 30-digit Decimal."""
    getcontext().prec = 30
    p, qd = Decimal(1) - Decimal(repr(q)), Decimal(repr(q))
    half = Decimal(1) / 2
    R = [Decimal(0)] * (K + 2)
    L = [Decimal(0)] * (K + 2)
    R[1], L[0] = half, half
    for n in range(2, N + 1):
        R2 = [Decimal(0)] * (K + 2)
        L2 = [Decimal(0)] * (K + 2)
        for k in range(1, min(n, K + 1) + 1):
            R2[k] = p * R[k - 1] + qd * L[k - 1]
        for k in range(0, min(n - 1, K + 1) + 1):
            L2[k] = p * L[k] + qd * R[k]
        R, L = R2, L2
    getcontext().prec = 60
    return [float((R[k] + L[k]).ln()) for k in range(K + 1)]


# ---------------------------------------------------------------- driver

def main():
    t0 = time.time()
    out = {"identity": {}, "rows": [], "bessel_check": [], "saddle_check": []}
    lines = []

    # P1: identity (E), exact
    mism = 0
    count = 0
    for qf in [Fraction(1, 2), Fraction(1, 3), Fraction(1, 7), Fraction(2, 11), Fraction(9, 10)]:
        for N in range(2, 41):
            row = dp_row(N, qf)
            for k in range(1, N):
                rc = runcount_exact(N, k, qf)
                rhs = identity_rhs_exact(N, k, qf)
                count += 1
                if not (row[k] == rc == rhs):
                    mism += 1
    out["identity"] = {"checked": count, "mismatches": mism}
    lines.append(f"P1 identity (E): {count} (N,k,q) checked exactly, mismatches = {mism}")

    # Bessel two-method check
    maxd = 0.0
    for x in [1e-6, 0.01, 0.1, 0.5, 1, 2, 5, 10, 30, 100, 250]:
        for j in (0, 1):
            a1, a2 = besse_series(j, x), besse_trap(j, x)
            d = abs(a1 / a2 - 1)
            maxd = max(maxd, d)
            out["bessel_check"].append([j, x, a1, a2, d])
    lines.append(f"Bessel e^-x I_j(x): series vs trapezoid, max relative difference = {maxd:.2e}")

    # saddle two-method check
    maxs = 0.0
    for (n1, n2, q) in [(1, 998, 0.3), (5, 993, 0.01), (499, 499, 0.2), (2, 97, 1e-4), (40, 57, 0.5)]:
        s1, s2 = saddle_closed(n1, n2, q), saddle_bisect(n1, n2, q)
        maxs = max(maxs, abs(s1 / s2 - 1))
        out["saddle_check"].append([n1, n2, q, s1, s2])
    lines.append(f"saddle s*: closed form vs bisection, max relative difference = {maxs:.2e}")

    qs = [0.5, 0.3, 0.1, 0.03, 0.01, 0.003, 0.001, 3e-4, 1e-4, 1e-5]
    Cemp = 0.0
    Cemp_at = None
    for N in [10, 20, 40, 100, 1000]:
        for q in qs:
            if N <= 40:
                qf = Fraction(q).limit_denominator(10 ** 7)
                rowA = [float(v) for v in dp_row(N, qf)]
                logP = [None] + [math.log(float(runcount_exact(N, k, qf))) for k in range(1, N)] + [None]
                qq = float(qf)
            else:
                rowA = dp_row(N, q)
                logP = [None] + [runcount_log(N, k, q) for k in range(1, N)] + [None]
                qq = q
            agree = max(abs(math.log(rowA[k]) - logP[k]) for k in range(1, N))
            rec = {"N": N, "q": qq, "dp_vs_runcount_maxlogdiff": agree}
            worst = {"U": (0, None), "G": (0, None), "TM": (0, None), "B": (0, None)}
            errs_U = {}
            for k in range(2, N - 1):
                lP = logP[k]
                eU = math.exp(lP - approx_U(N, k, qq)) - 1
                eG = math.exp(lP - approx_G(N, k, qq)) - 1
                eT = math.exp(lP - approx_TM(N, k, qq)) - 1
                eB = math.exp(lP - approx_B(N, k, qq)) - 1
                errs_U[k] = eU
                for name, e in (("U", eU), ("G", eG), ("TM", eT), ("B", eB)):
                    if abs(e) > abs(worst[name][0]):
                        worst[name] = (e, k)
                nmin = min(k - 1, N - k - 1)
                if qq <= 0.5 and nmin * abs(eU) > Cemp:
                    Cemp = nmin * abs(eU)
                    Cemp_at = (N, qq, k, eU)
            kc = N // 2
            rec["center_err"] = {"U": errs_U[kc],
                                 "G": math.exp(logP[kc] - approx_G(N, kc, qq)) - 1,
                                 "TM": math.exp(logP[kc] - approx_TM(N, kc, qq)) - 1,
                                 "B": math.exp(logP[kc] - approx_B(N, kc, qq)) - 1}
            rec["worst"] = {kk: [vv[0], vv[1]] for kk, vv in worst.items()}
            rec["err_U_edge"] = {str(k): errs_U[k] for k in range(2, min(8, N - 1))}
            # second method for U: trapezoid Bessel and bisection saddle, at the worst U bin and centre
            for kk in {worst["U"][1], kc}:
                u1 = approx_U(N, kk, qq)
                u2 = approx_U(N, kk, qq, bessel=besse_trap, saddle=saddle_bisect)
                rec.setdefault("U_two_methods_logdiff", []).append([kk, u1 - u2])
            out["rows"].append(rec)
            lines.append(
                f"N={N:5d} q={qq:.1e} | dp/rc {agree:.1e} | centre U {errs_U[kc]:+.2e} G {rec['center_err']['G']:+.2e}"
                f" TM {rec['center_err']['TM']:+.2e} B {rec['center_err']['B']:+.2e} | worst U {worst['U'][0]:+.3e}@{worst['U'][1]}"
                f" G {worst['G'][0]:+.2e}@{worst['G'][1]} TM {worst['TM'][0]:+.2e}@{worst['TM'][1]} B {worst['B'][0]:+.2e}@{worst['B'][1]}")
            sys.stdout.flush()
    out["C_emp"] = {"value": Cemp, "at": Cemp_at}
    lines.append(f"C_emp = max min(n1,n2)|err_U| = {Cemp:.4f} at (N,q,k,err) = {Cemp_at}")
    lines.append(f"elapsed {time.time() - t0:.1f} s")
    with open(os.path.join(DATA, "uniform-llt-verification.json"), "w") as f:
        json.dump(out, f, indent=1)
    with open(os.path.join(DATA, "uniform-llt-verification.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))


def main2():
    """Run 2: the proof-consistency checks, Paper A's bound, the sharp constant, q > 1/2."""
    t0 = time.time()
    out = {}
    lines = []
    # P9a: pointwise bound on F(pi, t) = A(pi, t) - pi sin t
    cF = 128 / (3 * math.pi ** 3)
    viol, nchk, worstF = 0, 0, 0.0
    for i in range(1, 400):
        pi = i / 400
        for j in range(1, 400):
            t = math.pi * j / 400
            F = argA(pi, t) - pi * math.sin(t)
            nchk += 1
            worstF = max(worstF, F / (pi * pi * t ** 3))
            if F < -1e-15 or F > cF * pi * pi * t ** 3 * (1 + 1e-12):
                viol += 1
    lines.append(f"P9 lemma F: {nchk} grid points, violations = {viol}, "
                 f"max F/(pi^2 t^3) = {worstF:.4f} (cF = {cF:.4f})")
    # P9a: moment lemma, Bessel closed forms against quadrature
    vx = 0
    for X in [1e-4, 0.01, 0.1, 0.3, 0.5, 1, 1.155, 1.3, 1.5, 1.7, 2, 3, 5, 10, 30, 100, 300]:
        r, k2, k3 = kappa_moments(X)
        ok = (1 / r <= 1 + 2 / X) and (k2 <= min(1.5, 2 / X ** 2)) and (k3 <= min(2.5, 8 / X ** 3))
        Mq = 20000
        h = math.pi / Mq
        Z = S2 = S3 = 0.0
        for ii in range(Mq):
            t = (ii + 0.5) * h
            kap = 1 - math.cos(t)
            g = math.exp(-X * kap)
            Z += g
            S2 += g * kap ** 2
            S3 += g * kap ** 3
        if not ok:
            vx += 1
        out.setdefault("moments", []).append([X, 1 / r, k2, k3, X * X * k2, X ** 3 * k3,
                                              abs(S2 / Z - k2), abs(S3 / Z - k3)])
    mo = out["moments"]
    lines.append("P9 lemma M (1/rho <= 1+2/x, <k^2> <= min(3/2,2/x^2), <k^3> <= min(5/2,8/x^3)): "
                 f"violations = {vx}; max x^2<k^2> = {max(r_[4] for r_ in mo):.4f}, "
                 f"max x^3<k^3> = {max(r_[5] for r_ in mo):.4f}, "
                 f"Bessel vs quadrature max diff = {max(max(r_[6], r_[7]) for r_ in mo):.1e}")

    # P9b, P10: |err_U| <= E_int <= E on sampled bins, and the Fourier representation of P_N(k)
    viol_int = viol_E = 0
    worst_mod_ratio = 0.0
    rep_diff = 0.0
    samples = []
    for N in [10, 20, 100, 1000]:
        for q in [0.5, 0.3, 0.1, 0.03, 0.01, 0.001, 1e-4]:
            ks = sorted(set([2, 3, 4, 5, 8, 12, N // 4, N // 2 - 1, N // 2]) & set(range(2, N - 1)))
            for k in ks:
                lP = runcount_log(N, k, q)
                e = abs(math.exp(lP - approx_U(N, k, q)) - 1)
                E = theorem_bound(N, k, q)
                Eint, lPf, wm = intermediate_bound(N, k, q, Mq=2000 if N < 1000 else 4000)
                worst_mod_ratio = max(worst_mod_ratio, wm)
                rep_diff = max(rep_diff, abs(lPf - lP))
                if e > Eint * (1 + 1e-9):
                    viol_int += 1
                if Eint > E * (1 + 1e-9):
                    viol_E += 1
                samples.append([N, q, k, e, Eint, E])
    out["bound_samples"] = samples
    lines.append(f"P9 chain: {len(samples)} sampled (N,k,q): violations |err_U|>E_int: {viol_int}, "
                 f"E_int>E: {viol_E}; max (g-|psi|)/(g min(1,4k^2V)) = {worst_mod_ratio:.4f}; "
                 f"Fourier representation vs run-count: max |dlogP| = {rep_diff:.1e}")
    for (N, q, k) in [(1000, 0.5, 500), (1000, 0.3, 500), (100, 0.5, 50), (1000, 0.5, 3),
                      (1000, 0.001, 500), (1000, 0.001, 2), (1000, 1e-4, 500)]:
        row = [r_ for r_ in samples if r_[0] == N and abs(r_[1] - q) < 1e-15 and r_[2] == k]
        if row:
            _, _, _, e, Eint, E = row[0]
            lines.append(f"   N={N} q={q} k={k}: |err_U|={e:.3e}  E_int={Eint:.3e}  E={E:.3e}  "
                         f"E/|err|={E / e:.1f}  E_int/|err|={Eint / e:.1f}")

    # P11: Paper A bound for B
    vb = nb = 0
    for N in [20, 100, 1000]:
        for q in [0.01, 0.001, 1e-4, 1e-5]:
            u = q / (1 - q)
            for k in range(1, N):
                eB = math.exp(runcount_log(N, k, q) - approx_B(N, k, q)) - 1
                nb += 1
                if not (-1e-12 <= -eB <= N * u * u / 2 + u + 1e-12):
                    vb += 1
    lines.append(f"P11 Paper A bound 0 <= -err_B <= N u^2/2 + u: {nb} bins, violations = {vb}")

    # P8: sharp constant at N = 10^4
    for q in [0.5, 0.3]:
        N, K = 10000, 400
        ld = dp_low_bins(N, q, K)
        best = (0, None, None)
        agree = 0.0
        for k in range(2, K + 1):
            lr = runcount_log(N, k, q)
            agree = max(agree, abs(ld[k] - lr))
            e = math.exp(lr - approx_U(N, k, q)) - 1
            if (k - 1) * abs(e) > best[0]:
                best = ((k - 1) * abs(e), k, e)
        e3 = math.exp(runcount_log(N, 3, q) - approx_U(N, 3, q)) - 1
        out.setdefault("sharp", []).append([N, q, best, agree, e3])
        lines.append(f"P8 N={N} q={q}: max_(2<=k<=400) n1|err_U| = {best[0]:.4f} at k={best[1]} "
                     f"(err {best[2]:+.4e}); err_U(k=3) = {e3:+.4f}; "
                     f"restricted recursion vs run-count max |dlogP| = {agree:.1e}")

    # P12: anti-persistent side
    for (N, q, k) in [(101, 0.999, 50), (100, 0.999, 50), (101, 0.9, 50), (1000, 0.99, 400)]:
        lP = runcount_log(N, k, q)
        e = math.exp(lP - approx_U(N, k, q)) - 1
        extra = ""
        if N <= 101:
            ld = math.log(float(dp_row(N, Fraction(q).limit_denominator(10 ** 6))[k]))
            extra = f"  (exact recursion vs run-count |dlogP| = {abs(ld - lP):.1e})"
        lines.append(f"P12 N={N} q={q} k={k}: err_U = {e:+.4f}" + extra)
    lines.append(f"elapsed {time.time() - t0:.1f} s")
    with open(os.path.join(DATA, "uniform-llt-verification-run2.json"), "w") as f:
        json.dump(out, f, indent=1)
    with open(os.path.join(DATA, "uniform-llt-verification-run2.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))


def centre_S_coeffs(N):
    """Integer coefficients W(N, N/2, j) of S_N(u) = P_N(N/2)/P_N(0) (Paper A, eq:SN), N even."""
    a = b = N // 2
    W = [0] * N
    for j in range(1, N):
        if j % 2 == 1:
            i = (j + 1) // 2
            W[j] = 2 * math.comb(a - 1, i - 1) * math.comb(b - 1, i - 1)
        else:
            i = j // 2
            W[j] = math.comb(a - 1, i) * math.comb(b - 1, i - 1) + math.comb(a - 1, i - 1) * math.comb(b - 1, i)
    return W


def exact_uN(N):
    """Root of S_N(u) = 1 by bisection in 50-digit Decimal."""
    getcontext().prec = 50
    W = [Decimal(w) for w in centre_S_coeffs(N)]
    lo, hi = Decimal(0), Decimal(1) / 2
    for _ in range(170):
        mid = (lo + hi) / 2
        val = Decimal(0)
        for w in reversed(W):          # Horner
            val = val * mid + w
        if val > 1:
            hi = mid
        else:
            lo = mid
    getcontext().prec = 60
    return (lo + hi) / 2


def centre_qU(N, bessel=besse_series):
    """Root q of 2 q e^{-x}(I_0+I_1)(x) = p^{N-1}, x = (N-2)pq."""
    def f(q):
        p = 1 - q
        x = (N - 2) * p * q
        return math.log(2 * q) + math.log(bessel(0, x) + bessel(1, x)) - (N - 1) * math.log(p)
    lo, hi = 1e-9, 0.5
    for _ in range(100):
        mid = 0.5 * (lo + hi)
        if f(mid) > 0:
            hi = mid
        else:
            lo = mid
    return 0.5 * (lo + hi)


def paperA_uB(N, bessel=besse_series):
    """Paper A: x_B solves 2x(I_0(2x)+I_1(2x)) = N/2, u_B = x_B/(N/2)."""
    h = N / 2
    lo, hi = 1e-9, 50.0
    for _ in range(100):
        mid = 0.5 * (lo + hi)
        # log of 2x e^{2x} (e^{-2x}I_0 + e^{-2x}I_1)(2x)
        val = math.log(2 * mid) + 2 * mid + math.log(bessel(0, 2 * mid) + bessel(1, 2 * mid))
        if val > math.log(h):
            hi = mid
        else:
            lo = mid
    return 0.5 * (lo + hi) / h


def main3():
    t0 = time.time()
    lines = []
    for N in [100, 400, 1600]:
        uN = exact_uN(N)
        pN = 1 / (1 + uN)
        qN = float(1 - pN)
        qU1 = centre_qU(N)
        qU2 = centre_qU(N, bessel=besse_trap)
        uB1 = paperA_uB(N)
        uB2 = paperA_uB(N, bessel=besse_trap)
        lines.append(f"N={N}: p_N = {float(pN):.10f}; q_U/q_N - 1 = {qU1 / qN - 1:+.3e} (trapezoid: {qU2 / qN - 1:+.3e}); "
                     f"u_B/u_N = {uB1 / float(uN):.5f} (trapezoid: {uB2 / float(uN):.5f}); "
                     f"ratio of relative errors = {abs(qU1 / qN - 1) / abs(uB1 / float(uN) - 1):.3f}")
    lines.append(f"elapsed {time.time() - t0:.1f} s")
    with open(os.path.join(DATA, "uniform-llt-verification-run3.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    if "--run2" in sys.argv:
        main2()
    elif "--run3" in sys.argv:
        main3()
    else:
        main()
