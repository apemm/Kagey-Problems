"""Repair-pass checks for the Paper B tie notes (research131/B_tie.md), registered in
data/ledger_B_tie.md as T1(e') and T4'' before this script was run.

Standard library only (fractions, decimal, math, time). Output: data/B_tie_repair_output.txt.

T1(e')  exact Legendre identity Hess I(alpha) * Sigma_alpha = identity on K_k, at rational points
        alpha_i = x_i^2 (x a rational point of the unit sphere), k = 2..6.
        Hess I: closed form in exact Fractions (method 1) and 80-digit Decimal central
        differences (method 2). Sigma: Doob-chain fundamental matrix, exact (as in T1(c)).
T4''    K_3, mu = (1/2,1/2,0), N = 300: the T4 line search for the full-face maximum (M1, same
        code path as verify_general_start.T4), checked globally by a forward DP over all bins (M3)
        at u_up (1 -+ 1e-7).
T4'''   the same global DP check at the reported T4 cell N = 1002 (registered after T4'' ran).
        The module array (standard library) keeps the DP buffers small.
"""
import math
import time
from array import array
from decimal import Decimal, getcontext
from fractions import Fraction as Fr

from verify_general_start import (a_const, bisect_root, inv_frac, m1_coeffs, m1_logratio,
                                  m2_coeffs, m2_logratio)

OUT = []


def say(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    OUT.append(s)


# ----------------------------------------------------------------------------------------
# T1(e')
# ----------------------------------------------------------------------------------------
def sphere_point(t):
    """inverse stereographic projection: rational point of the unit sphere in R^{len(t)+1}."""
    s = sum(ti * ti for ti in t)
    return [(1 - s) / (1 + s)] + [2 * ti / (1 + s) for ti in t]


def doob_sigma(x):
    """exact Sigma (Gamma without row/col 1) for the Doob chain G_ij = x_j/x_i."""
    k = len(x)
    S = sum(xi * xi for xi in x)
    alpha = [xi * xi / S for xi in x]
    G = [[Fr(0)] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            if i != j:
                G[i][j] = x[j] / x[i]
        G[i][i] = -sum(G[i][j] for j in range(k) if j != i)
    for j in range(k):
        assert sum(alpha[i] * G[i][j] for i in range(k)) == 0
    B = [[alpha[j] - G[i][j] for j in range(k)] for i in range(k)]
    Binv = inv_frac(B)
    Z = [[Binv[i][j] - alpha[j] for j in range(k)] for i in range(k)]
    Gam = [[alpha[i] * Z[i][j] + alpha[j] * Z[j][i] for j in range(k)] for i in range(k)]
    return [row[1:] for row in Gam[1:]], alpha


def hess_I_exact(x):
    """Hess_{alpha'} of I = k - A^2, A = sum x_i, x_i = sqrt(alpha_i), alpha_1 = 1 - sum alpha'."""
    k = len(x)
    m = k - 1
    A = sum(x)
    g = [Fr(1, 2) / x[j] - Fr(1, 2) / x[0] for j in range(1, k)]
    H = [[Fr(0)] * m for _ in range(m)]
    for a in range(m):
        for b in range(m):
            hA = -Fr(1, 4) / x[0] ** 3 - (Fr(1, 4) / x[a + 1] ** 3 if a == b else 0)
            H[a][b] = -(2 * g[a] * g[b] + 2 * A * hA)
    return H


def hess_I_decimal(alpha):
    getcontext().prec = 80
    k = len(alpha)
    m = k - 1
    a0 = [Decimal(a.numerator) / Decimal(a.denominator) for a in alpha[1:]]
    h = Decimal("1e-25")

    def I(ap):
        a1 = 1 - sum(ap)
        A = a1.sqrt() + sum(q.sqrt() for q in ap)
        return k - A * A

    H = [[Decimal(0)] * m for _ in range(m)]
    for i in range(m):
        for j in range(m):
            def sh(di, dj):
                ap = a0[:]
                ap[i] += di
                ap[j] += dj
                return I(ap)
            H[i][j] = (sh(h, h) - sh(h, -h) - sh(-h, h) + sh(-h, -h)) / (4 * h * h)
    return H


def det_frac(M):
    M = [row[:] for row in M]
    n = len(M)
    det = Fr(1)
    for c in range(n):
        piv = next(r for r in range(c, n) if M[r][c] != 0)
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            det = -det
        det *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            for cc in range(c, n):
                M[r][cc] -= f * M[c][cc]
    return det


def T1e_prime():
    say("=" * 90)
    say("T1(e')  exact Legendre identity: Hess_{alpha'} I * Sigma_alpha = identity (K_k)")
    say("-" * 90)
    all_i = all_iii = True
    worst_fd = 0.0
    for k in range(2, 7):
        for trial in range(3):
            t = [Fr(i + 1 + trial, 3 * (i + 2) + 2 * trial + 1) for i in range(k - 1)]
            assert sum(ti * ti for ti in t) < 1
            x = sphere_point(t)
            assert all(xi > 0 for xi in x) and sum(xi * xi for xi in x) == 1
            Sig, alpha = doob_sigma(x)
            H = hess_I_exact(x)
            m = k - 1
            prod = [[sum(H[i][l] * Sig[l][j] for l in range(m)) for j in range(m)] for i in range(m)]
            ident = all(prod[i][j] == (1 if i == j else 0) for i in range(m) for j in range(m))
            detprod = det_frac(H) * det_frac(Sig)
            Hd = hess_I_decimal(alpha)
            rel = 0.0
            for i in range(m):
                for j in range(m):
                    ex = Decimal(H[i][j].numerator) / Decimal(H[i][j].denominator)
                    rel = max(rel, float(abs(Hd[i][j] - ex) / abs(ex)))
            worst_fd = max(worst_fd, rel)
            all_i &= ident
            all_iii &= (detprod == 1)
            say(f"   k={k} x={[str(xi) for xi in x]}")
            say(f"        Hess I * Sigma == I exactly: {ident}   det Hess I * det Sigma == 1: {detprod == 1}"
                f"   Decimal FD vs exact Hess, worst rel: {rel:.1e}")
    say(f"   (i) all 15 points identity: {all_i}   (ii) worst FD rel diff {worst_fd:.1e}"
        f" (<= 1e-20: {worst_fd <= 1e-20})   (iii) all det products 1: {all_iii}")


# ----------------------------------------------------------------------------------------
# T4''
# ----------------------------------------------------------------------------------------
def dp_all_fast(N, u, mu3):
    """forward DP over positions; returns {(n1,n2,n3): P_N(n)} (floats)."""
    d = 3
    p = 1 / (1 + (d - 1) * u)
    r = (1 - p) / (d - 1)
    size = N + 2
    cur = [[array("d", bytes(8 * size)) for _ in range(size)] for _ in range(3)]
    nxt = [[array("d", bytes(8 * size)) for _ in range(size)] for _ in range(3)]
    cur[0][1][0] = mu3[0]
    cur[1][0][1] = mu3[1]
    cur[2][0][0] = mu3[2]
    for s in range(1, N):
        # s letters placed; states with n1 + n2 <= s; next step has n1 + n2 <= s + 1
        for c in range(3):
            X = nxt[c]
            for n1 in range(s + 2):
                row = X[n1]
                for n2 in range(s + 2 - n1):
                    row[n2] = 0.0
        c0, c1, c2 = cur
        x0, x1, x2 = nxt
        for n1 in range(s + 1):
            r0, r1, r2 = c0[n1], c1[n1], c2[n1]
            y0 = x0[n1 + 1]
            y1 = x1[n1]
            y2 = x2[n1]
            for n2 in range(s + 1 - n1):
                v0 = r0[n2]
                v1 = r1[n2]
                v2 = r2[n2]
                if v0 == 0.0 and v1 == 0.0 and v2 == 0.0:
                    continue
                y0[n2] += v0 * p + (v1 + v2) * r
                y1[n2 + 1] += v1 * p + (v0 + v2) * r
                y2[n2] += v2 * p + (v0 + v1) * r
        cur, nxt = nxt, cur
    P = {}
    for n1 in range(N + 1):
        for n2 in range(N + 1 - n1):
            v = cur[0][n1][n2] + cur[1][n1][n2] + cur[2][n1][n2]
            if v > 0:
                P[(n1, n2, N - n1 - n2)] = v
    return P, p


def T4pp(N=300, pl=-0.291539, pu=-0.211297, tolv=0.0551, t_up_ref=None, n_ref=None,
         title="T4''  K_3, mu=(1/2,1/2,0), N=300: M1 line search checked globally by a DP over all bins"):
    say("=" * 90)
    say(title)
    say("-" * 90)
    mu3 = [0.5, 0.5, 0.0]
    t0 = time.time()
    a2 = a_const(2)
    L = math.log(N)
    zg = L - 0.5 * math.log(L) + a2
    mmax = min(N, int(30 + 5 * zg))
    tcoord = lambda u: N * u - L + 0.5 * math.log(L)
    # ---- same code path as verify_general_start.T4 ----
    ne = [N // 2, N // 2]
    Re = m1_coeffs(ne, N, [0.5, 0.5], mmax)
    Ce = m2_coeffs(ne, N, [1.0, 1.0], mmax)
    ledge = lambda u: m1_logratio(Re, 2, N, u)
    f_low1 = lambda u: ledge(u) - math.log(0.5)
    f_low2 = lambda u: m2_logratio(Ce, 2, N, u)
    ulow1 = bisect_root(f_low1, 0.3 * zg / N, 2.0 * zg / N)
    ulow2 = bisect_root(f_low2, 0.3 * zg / N, 2.0 * zg / N)
    cache = {}

    def full_val(n3, u):
        n12 = N - n3
        n1, n2 = (n12 + 1) // 2, n12 // 2
        key = (n1, n2, n3)
        if key not in cache:
            cache[key] = m1_coeffs([n1, n2, n3], N, mu3, mmax)
        return m1_logratio(cache[key], 3, N, u)

    def full_max(u, s0):
        s = s0
        step = max(1, N // 64)
        val = full_val(s, u)
        while step >= 1:
            moved = True
            while moved:
                moved = False
                for cand in (s - step, s + step):
                    if 1 <= cand <= N - 2:
                        vc = full_val(cand, u)
                        if vc > val:
                            s, val, moved = cand, vc, True
                            break
            step //= 2
        return s, val

    state = {"s": int(N * (1 / 3 - 1 / (9 * zg)))}

    def f_up(u):
        s, val = full_max(u, state["s"])
        state["s"] = s
        return val - ledge(u)

    zlo = pu - 0.25 + L - 0.5 * math.log(L)
    zhi = pu + 0.25 + L - 0.5 * math.log(L)
    uup = bisect_root(f_up, zlo / N, zhi / N, it=60, tol=1e-13)
    s_hat, _ = full_max(uup, state["s"])
    best = None
    for dn3 in range(-2, 3):
        n3 = s_hat + dn3
        for dd in range(-3, 4):
            n12 = N - n3
            if (n12 + dd) % 2:
                continue
            n1 = (n12 + dd) // 2
            n2 = n12 - n1
            if min(n1, n2, n3) < 1:
                continue
            val = m1_logratio(m1_coeffs([n1, n2, n3], N, mu3, mmax), 3, N, uup)
            if best is None or val > best[0]:
                best = (val, n1, n2, n3)
    # ---- end of the T4 code path ----
    tl1, tl2, tu = tcoord(ulow1), tcoord(ulow2), tcoord(uup)
    zup = N * uup
    nmax = (best[1], best[2], best[3])
    say(f"N={N}: t_low(M1)={tl1:+.8f} t_low(A's S_N=1, M2)={tl2:+.8f} rel u diff={abs(ulow1/ulow2-1):.1e}")
    say(f"        t_up={tu:+.8f}  width={tu-tl1:.6f}   predicted t_low={pl:+.6f} t_up={pu:+.6f}")
    say(f"        t_low-pred={tl1-pl:+.6f} (tol {tolv}, ok {abs(tl1-pl)<=tolv})"
        f"  t_up-pred={tu-pu:+.6f} (tol {tolv}, ok {abs(tu-pu)<=tolv})")
    say(f"        M1 full-face maximiser at t_up: n={nmax}  |n1-n2|={abs(nmax[0]-nmax[1])}"
        f"  z(1/3-n3/N)={zup*(1/3-nmax[2]/N):.5f}  [M1 part {time.time()-t0:.1f}s]")
    swap = {nmax, (nmax[1], nmax[0], nmax[2])}
    ok_iv = True
    for lab, u in (("u_-", uup * (1 - 1e-7)), ("u_+", uup * (1 + 1e-7))):
        t1 = time.time()
        P, p = dp_all_fast(N, u, mu3)
        mass = sum(P.values())
        mx = max(P.values())
        modes = sorted(n for n, v in P.items() if v >= mx * (1 - 1e-12))
        fullP = {n: v for n, v in P.items() if min(n) >= 1}
        fmx = max(fullP.values())
        fmodes = sorted(n for n, v in fullP.items() if v >= fmx * (1 - 1e-12))
        m1v = m1_logratio(m1_coeffs(list(nmax), N, mu3, mmax), 3, N, u)
        dpv = math.log(P[nmax] / p ** (N - 1))
        say(f"   DP at {lab} (t={tcoord(u):+.8f}): total mass {mass:.15f}; global modes {modes};"
            f" full-face DP max at {fmodes}; |log DP - log M1| at M1 maximiser = {abs(dpv-m1v):.1e}"
            f"  [{time.time()-t1:.1f}s]")
        if lab == "u_-":
            ok_iv &= (modes == [(N // 2, N // 2, 0)])
        else:
            ok_iv &= (set(modes) == swap)
        ok_iv &= set(fmodes) <= swap and len(set(fmodes)) >= 1
    say(f"   (iv) global-mode prediction holds: {ok_iv}")
    if t_up_ref is not None:
        say(f"   reproduces reference t_up {t_up_ref:+.8f}: diff {tu - t_up_ref:+.1e}"
            f" (<= 1e-8: {abs(tu - t_up_ref) <= 1e-8});  maximiser == {n_ref}: {nmax == n_ref}")
    say(f"   total {time.time()-t0:.1f}s")


def main():
    t0 = time.time()
    T1e_prime()
    T4pp()
    T4pp(N=1002, pl=-0.340235, pu=-0.323179, tolv=0.0476, t_up_ref=-0.27171620,
         n_ref=(345, 345, 312),
         title="T4'''  same global DP check at the T4 cell N = 1002"
               " (t tolerances printed are T4's, already killed there)")
    say(f"total time {time.time()-t0:.1f}s")
    with open("data/B_tie_repair_output.txt", "w", encoding="utf-8") as fh:
        fh.write("\n".join(OUT) + "\n")


if __name__ == "__main__":
    main()
