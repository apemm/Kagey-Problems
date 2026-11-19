"""Checks of the face maxima on reducible faces and of the counts near a facet, Paper C1.

Section `sec:reducible-max` (Theorem `thm:reducible`) and Section `sec:layer-counts`
(Theorems `thm:pair-counts` and `thm:layer-counts`) of problem131_chains.tex.

  A. Theorem `thm:pair-counts`(a), the discrete Pedler formula, for the pair face F = {1,2} of a
     chain on three states with q12 = 3/2, q21 = 2, killing rates 1/2 and 1/3 to state 3 and
     mu = (2/5, 1/5, 2/5), with j = 1 and i = 2. Exact rational arithmetic: the formula against an
     enumeration of all paths in F, for every N <= 12, h = 1/7 and 1/13 and every 1 <= n_i < N,
     and P_N'(n-hat) = mu_j p_j^(N'-1).
  B. Theorem `thm:pair-counts`(c) and (d) for the same face in floating point. The two-sided
     bound on R / K^h holds on a grid with N' up to 10^4, n_i <= N' and T from 1/2 to N'^(1/2).
     Where h S <= 1, |K^h / (h K(x,S)) - 1| <= 2 (h + h S).
  C. Theorem `thm:layer-counts` for the cycle q12 = q23 = q31 = 2, q21 = q32 = q13 = 1 of
     Proposition `prop:layer-cubic`(e), uniform start, i = 3 and beta = (1/2, 1/2). The exact
     laws P_N(n) and P_N'(n-hat) come from a forward recursion over the counts. The lattice
     kernel is the contour integral of Section `sec:layer-counts`, with J_G(beta,z) and C_G(beta,z)
     from the closed forms of Lemma `lem:L-two`, and h = T/N with N = N' + n_i. The error E of
     part (a) satisfies 0 < E <= T^2/N at T = 8, n_3 = 10 and N' = 200 to 1600, and at T = 4,
     n_3 = 1, N' = 1600, and it falls by a factor between 2 and 3 each time N' doubles. Part (b),
     the lattice kernel against h K_beta(x - h, S), holds with a difference below T^2/N.
  D. Theorem `thm:reducible` for the face {1} -> {2,3} with q12 = q23 = q32 = 1 and the start in
     state 1. Here k_F = 3, k* = 2, lambda_F = 0, p_F = 3/2 and K^red_F = sqrt(2/pi). The face
     maximum is computed exactly from the block factorization and the run expansion of the block
     {2,3}, maximized over n_1 <= 4 and n_2 at N = 40000. The local slope of log M_F in log T lies
     within 0.001 of 3/2 for T = 8 to 20 (the bounds of Theorem `thm:first`(ii) have the powers 1
     and 2), and M_F / (N^-2 T^(3/2)) is within 0.05% of sqrt(2/pi). The block engine agrees with
     a brute-force recursion over (counts, state) at N = 10.

Every check is an assertion. Nothing in the paper is deduced from these numbers.
Needs numpy and scipy. Run:  py -I verify_counts.py   (a few seconds)
"""
import itertools
import math
from fractions import Fraction

import numpy as np
from scipy.special import gammaln, ive

CHECKS = 0


def ok(cond, what):
    global CHECKS
    if not cond:
        raise AssertionError(what)
    CHECKS += 1
    print("  ok   ", what, flush=True)


def logsumexp(v):
    v = np.asarray(v, float)
    m = np.max(v)
    return m + math.log(np.sum(np.exp(v - m)))


def lbinom(n, k):
    return gammaln(n + 1) - gammaln(k + 1) - gammaln(n - k + 1)


# ---------------------------------------------------------------- A, B: the pair face
def pair_rates():
    # states 0 = j, 1 = i, 2 = the killing state
    q = {(0, 1): Fraction(3, 2), (1, 0): Fraction(2), (0, 2): Fraction(1, 2), (1, 2): Fraction(1, 3)}
    mu = (Fraction(2, 5), Fraction(1, 5), Fraction(2, 5))
    return q, mu


def pair_formula(ni, Np, h, qji, qij, qj, qi, muj, mui):
    """R of Theorem thm:pair-counts(a), in the arithmetic of the inputs."""
    om = qji * qij
    c = [1, qji + mui / muj * qij, mui / muj * om]
    pi_, pj = 1 - h * qi, 1 - h * qj
    tot = 0
    for K in range(1, ni + 1):
        s = 0
        for e in range(3):
            m = K - e
            if 0 <= m <= Np - 1:
                s += c[e] * h ** e * math.comb(Np - 1, m) * (h * h * om / pj) ** m
        tot += math.comb(ni - 1, K - 1) * pi_ ** (ni - K) * s
    return tot


def part_A():
    print("A. The discrete Pedler formula against all paths, exact arithmetic")
    q, mu = pair_rates()
    qj = q[(0, 1)] + q[(0, 2)]
    qi = q[(1, 0)] + q[(1, 2)]
    worst = 0
    rows = 0
    for h in (Fraction(1, 7), Fraction(1, 13)):
        M = [[1 - h * qj, h * q[(0, 1)]], [h * q[(1, 0)], 1 - h * qi]]
        for N in range(2, 13):
            law = {}
            for w in itertools.product((0, 1), repeat=N):
                p = mu[w[0]]
                for a, b in zip(w, w[1:]):
                    p *= M[a][b]
                ni = sum(w)
                law[ni] = law.get(ni, 0) + p
            if law[0] != mu[0] * (1 - h * qj) ** (N - 1):
                worst += 1
            for ni in range(1, N):
                Np = N - ni
                Pprime = mu[0] * (1 - h * qj) ** (Np - 1)
                R = pair_formula(ni, Np, h, q[(0, 1)], q[(1, 0)], qj, qi, mu[0], mu[1])
                if law[ni] != Pprime * R:
                    worst += 1
                rows += 1
    ok(worst == 0, f"P_N(N,0) = mu_j p_j^(N-1) and P_N(n) = mu_j p_j^(N'-1) R exactly in all {rows} cases "
       f"(N <= 12, h = 1/7 and 1/13, 1 <= n_i < N)")


def log_terms_R(ni, Np, h, qji, qij, qj, qi, muj, mui):
    om = qji * qij
    c = [1.0, qji + mui / muj * qij, mui / muj * om]
    pi_, pj = 1 - h * qi, 1 - h * qj
    out = []
    for e in range(3):
        K = np.arange(max(1, e), ni + 1)
        m = K - e
        keep = m <= Np - 1
        K, m = K[keep], m[keep]
        if len(K) == 0:
            continue
        lt = (lbinom(ni - 1, K - 1) + (ni - K) * math.log(pi_) + math.log(c[e]) + e * math.log(h)
              + lbinom(Np - 1, m) + m * math.log(h * h * om / pj))
        out.append(lt)
    return logsumexp(np.concatenate(out))


def log_Kh(ni, Np, h, qji, qij, qi, muj, mui):
    om = qji * qij
    c = [1.0, qji + mui / muj * qij, mui / muj * om]
    S = h * Np
    pi_ = 1 - h * qi
    out = []
    for e in range(3):
        K = np.arange(max(1, e), ni + 1)
        m = K - e
        lt = (lbinom(ni - 1, K - 1) + (ni - K) * math.log(pi_) + K * math.log(h) + math.log(c[e])
              + m * math.log(S * om) - gammaln(m + 1))
        out.append(lt)
    return logsumexp(np.concatenate(out))


def log_K_pedler(x, S, qji, qij, qi, muj, mui):
    om = qji * qij
    c1 = qji + mui / muj * qij
    c2 = mui / muj * om
    z = 2 * math.sqrt(om * S * x)
    i0, i1 = ive(0, z), ive(1, z)
    br = math.sqrt(om * S / x) * i1 + c1 * i0 + c2 * math.sqrt(x / (om * S)) * i1
    return z - qi * x + math.log(br)


def part_B():
    print("B. The bounds of Theorem thm:pair-counts(c) and part (d)")
    q, mu = pair_rates()
    qji, qij = float(q[(0, 1)]), float(q[(1, 0)])
    qj, qi = qji + float(q[(0, 2)]), qij + float(q[(1, 2)])
    muj, mui = float(mu[0]), float(mu[1])
    om = qji * qij
    rows = viol = 0
    dworst = 0.0
    for Np in (10, 100, 1000, 10000):
        for T in (0.5, 1.0, 3.0, 10.0, math.sqrt(Np)):
            for ni in (1, 2, 5, 20, 200, 2000):
                if ni > Np:
                    continue
                N = Np + ni
                h = T / N
                if h * max(qi, qj) > 0.5:
                    continue
                lR = log_terms_R(ni, Np, h, qji, qij, qj, qi, muj, mui)
                lK = log_Kh(ni, Np, h, qji, qij, qi, muj, mui)
                ratio = math.exp(lR - lK)
                S = h * Np
                U = ni * h * S * om / (1 - h * qi)
                lo = 1 - (U + 2 * math.sqrt(U) + 2) / (2 * Np)
                hi = math.exp(2 * h * qj * (1 + 2 * math.sqrt(U)))
                rows += 1
                if not (lo - 1e-12 <= ratio <= hi + 1e-12):
                    viol += 1
                if h * S <= 1:
                    x = h * ni
                    d = abs(math.exp(lK - math.log(h) - log_K_pedler(x, S, qji, qij, qi, muj, mui)) - 1)
                    dworst = max(dworst, d / (h + h * S))
    ok(viol == 0, f"the two-sided bound of part (c) holds in all {rows} cells (N' <= 10^4, n_i <= N')")
    ok(dworst <= 2.0, f"part (d): max |K^h/(h K) - 1| / (h + h S) = {dworst:.3f} <= 2 over the cells with h S <= 1")


# ---------------------------------------------------------------- C: the 3-cycle
CYC = np.array([[0.0, 2.0, 1.0], [1.0, 0.0, 2.0], [2.0, 1.0, 0.0]])
np.fill_diagonal(CYC, -CYC.sum(axis=1))


def exact_three(Q, mu, h, n):
    """P(composition n) for the chain I + hQ on 3 states, forward recursion over (c0, c2, state);
    the count of state 1 is the step number minus c0 and c2."""
    P = np.eye(3) + h * Q
    n0, n1, n2 = n
    N = n0 + n1 + n2
    A = np.zeros((n0 + 2, n2 + 2, 3))
    A[1, 0, 0] = mu[0]
    A[0, 0, 1] = mu[1]
    A[0, 1, 2] = mu[2]
    for step in range(1, N):
        B = np.zeros_like(A)
        for b in range(3):
            tmp = A @ P[:, b]
            if b == 0:
                B[1:, :, 0] = tmp[:-1, :]
            elif b == 1:
                B[:, :, 1] = tmp
            else:
                B[:, 1:, 2] = tmp[:, :-1]
        # drop the states whose count of state 1 would be negative or too large
        c0 = np.arange(n0 + 2)[:, None]
        c2 = np.arange(n2 + 2)[None, :]
        c1 = step + 1 - c0 - c2
        bad = (c1 < 0) | (c1 > n1)
        B[bad, :] = 0.0
        A = B
    return A[n0, n2].sum()


def facet_functions(z):
    """J_G(beta,z) and C_G(beta,z) of Lemma lem:L-two for the cycle, G = {1,2}, i = 3, beta = (1/2,1/2)."""
    a12 = 2 + z
    a21 = 1 + 4 * z
    w = a12 * a21
    sw = np.sqrt(w)
    J = 3 - 2 * z - sw
    p1 = 1 / 3 + z * 2 / 3
    p2 = 1 / 3 + z * 1 / 3
    e1 = 1 + z
    e2 = 1 + 2 * z
    U = (p1 * e1 + p2 * e2) * sw
    V = p1 * a12 * e2 + p2 * a21 * e1
    C = (U + V) / (np.sqrt(4 * np.pi) * (w / 4) ** 0.25)
    return J, C


def lattice_kernel(n, S, h, rho=0.1, M=512):
    z = rho * np.exp(2j * np.pi * np.arange(M) / M)
    J0, C0 = facet_functions(0.0)
    J, C = facet_functions(z)
    lam = C / C0 * np.exp(S * (J0 - J))
    qi = 3.0
    w = (1 - h * qi + h / z) ** (n - 1)
    return (h * np.mean(w * lam / z)).real


def cont_kernel(x, S, rho=0.1, M=512):
    z = rho * np.exp(2j * np.pi * np.arange(M) / M)
    J0, C0 = facet_functions(0.0)
    J, C = facet_functions(z)
    lam = C / C0 * np.exp(S * (J0 - J))
    return (np.exp(-3.0 * x) * np.mean(np.exp(x / z) * lam / z)).real


def part_C():
    print("C. Theorem thm:layer-counts on the non-reversible cycle, i = 3, beta = (1/2,1/2)")
    mu = np.array([1 / 3, 1 / 3, 1 / 3])
    J0, C0 = facet_functions(0.0)
    om = -(facet_functions(1e-6)[0] - facet_functions(-1e-6)[0]).real / 2e-6
    ok(abs(om - (2 + 9 / 4 * math.sqrt(2))) < 1e-6, f"omega_beta = {om:.6f} = 2 + (9/4) sqrt 2 from the closed form")
    # the kernel does not depend on the radius
    k1, k2 = lattice_kernel(10, 7.6, 0.04, rho=0.06), lattice_kernel(10, 7.6, 0.04, rho=0.15)
    ok(abs(k1 / k2 - 1) < 1e-12, f"the lattice kernel is the same on the radii 0.06 and 0.15 (difference {abs(k1/k2-1):.1e})")
    Es = []
    for Np, T, ni in ((200, 8.0, 10), (400, 8.0, 10), (800, 8.0, 10), (1600, 8.0, 10), (1600, 4.0, 1)):
        N = Np + ni
        h = T / N
        S = h * Np
        x = h * ni
        PN = exact_three(CYC, mu, h, (Np // 2, Np // 2, ni))
        # P_N'(n-hat): paths in {1,2} with composition (N'/2, N'/2)
        P0 = exact_three(CYC, mu, h, (Np // 2, Np // 2, 0))
        L = lattice_kernel(ni, S, h)
        E = PN / (P0 * L) - 1
        Kc = cont_kernel(x - h, S)
        dlat = L / (h * Kc) - 1
        ok(0 < E <= T * T / N and abs(dlat) <= T * T / N,
           f"N' = {Np}, T = {T:g}, n_3 = {ni}: E = {E:.4e}, T^2/N = {T*T/N:.4f}, E N/T^2 = {E*N/(T*T):.3f}, "
           f"K^h/(h K(x-h,S)) - 1 = {dlat:+.4e}")
        if T == 8.0:
            Es.append(E)
    fac = [Es[k] / Es[k + 1] for k in range(len(Es) - 1)]
    ok(all(2.0 <= f <= 3.0 for f in fac), "E falls by the factors " + ", ".join(f"{f:.2f}" for f in fac)
       + " as N' doubles from 200 to 1600 (T = 8)")


# ---------------------------------------------------------------- D: the reducible face
def block23_log(n2, n3, h, mcap):
    """log of G(n2,n3): start in 2, alternate 2,3,2,..., all rates 1, any end state."""
    m2 = np.arange(1, min(n2, mcap) + 1)
    out = []
    for d in (1, 0):  # m3 = m2 - 1 (end in 2) and m3 = m2 (end in 3)
        m3 = m2 - d
        keep = (m3 >= 1) & (m3 <= n3)
        a, b = m2[keep], m3[keep]
        if len(a) == 0:
            continue
        M = a + b
        lt = ((M - 1) * math.log(h) + lbinom(n2 - 1, a - 1) + lbinom(n3 - 1, b - 1)
              + (n2 + n3 - M) * math.log1p(-h))
        out.append(lt)
    return logsumexp(np.concatenate(out))


def face_log(n1, n2, n3, h, mcap):
    # mu_1 = 1, (1 - h q_1)^(n1 - 1), switch 1 -> 2 of probability h q_12 = h, then the block
    return (n1 - 1) * math.log1p(-h) + math.log(h) + block23_log(n2, n3, h, mcap)


def face_max_log(N, T):
    h = T / N
    mcap = int(T + 20 * math.sqrt(T) + 40)
    best = -np.inf
    for n1 in range(1, 5):
        l = N - n1
        f = lambda a: face_log(n1, a, l - a, h, mcap)
        lo, hi = 1, l - 1
        while hi - lo > 2:
            m1 = lo + (hi - lo) // 3
            m2 = hi - (hi - lo) // 3
            if f(m1) < f(m2):
                lo = m1
            else:
                hi = m2
        best = max(best, max(f(a) for a in range(max(1, lo - 3), min(l - 1, hi + 3) + 1)))
    return best


def part_D():
    print("D. Theorem thm:reducible on the face {1} -> {2,3}")
    # the block engine against a brute-force recursion at N = 10
    Q = np.array([[-1.0, 1.0, 0.0], [0.0, -1.0, 1.0], [0.0, 1.0, -1.0]])
    N, T = 10, 2.0
    h = T / N
    P = np.eye(3) + h * Q
    law = {}
    for w in itertools.product((0, 1, 2), repeat=N):
        if w[0] != 0:
            continue
        p = 1.0
        for a, b in zip(w, w[1:]):
            p *= P[a, b]
        if p == 0.0:
            continue
        c = (w.count(0), w.count(1), w.count(2))
        law[c] = law.get(c, 0.0) + p
    worst = 0.0
    for c, p in law.items():
        if min(c) >= 1:
            worst = max(worst, abs(math.exp(face_log(c[0], c[1], c[2], h, 50)) / p - 1))
    ok(worst < 1e-12, f"the block engine equals the brute-force law at N = 10 for all {sum(min(c) >= 1 for c in law)} "
       f"compositions with support F (max relative difference {worst:.1e})")
    K = math.sqrt(2 / math.pi)
    N = 40000
    eta = 0.05
    for T in (8.0, 10.0, 12.0, 15.0, 20.0):
        lm = face_max_log(N, T)
        ratio = math.exp(lm + 2 * math.log(N) - 1.5 * math.log(T)) / K
        slope = (face_max_log(N, T * (1 + eta)) - face_max_log(N, T * (1 - eta))) / math.log((1 + eta) / (1 - eta))
        ok(abs(slope - 1.5) <= 0.001 and abs(ratio - 1) <= 5e-4,
           f"N = {N}, T = {T:g}: local slope {slope:.4f} (bounds of thm:first(ii): 1 and 2), "
           f"M_F / (N^-2 T^1.5 sqrt(2/pi)) = {ratio:.5f}")


def main():
    part_A()
    part_B()
    part_C()
    part_D()
    print(f"verify_counts: all {CHECKS} checks passed")


if __name__ == "__main__":
    main()
