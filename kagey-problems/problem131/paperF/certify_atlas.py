"""Exact occupation law P_N for a fresh plus start, by the run recursion of Proposition prop:final-run.

Run law: the zeta law f(n) = n^(-alpha-1)/zeta(alpha+1), n >= 1, with alpha_+ = alpha_- = 1.5.
Fresh plus start. Output: data/atlas_N5000.json.

Run from the paper folder:  py -I certify_atlas.py            (N = 5000, the default)
                             py -I certify_atlas.py 1200      (any other N, written to data/atlas_N1200.json)

The recursion. Index a run start by (k, m), the numbers of plus and minus slots before it.
A[m][k] is the probability that a plus run starts after k plus and m minus slots, and B[m][k]
the same for a minus run. For a fresh plus start A[0] = e_0, and for k + m <= N - 1
    B[m][k] = sum_{l=1}^{k} f_+(l) A[m][k-l],      A[m][k] = sum_{l=1}^{m} f_-(l) B[m-l][k]   (m >= 1).
The final run is censored by the horizon, so
    P_N(N-m) += sum_k A[m][k] T_+(N-k-m),          P_N(k) += B[m][k] T_-(N-k-m).
This is Proposition prop:final-run with t = k + m. The cost is O(N^3).

Error control. Every quantity is a sum of products of nonnegative numbers. The inputs f and T are
converted from the midpoints of 128-bit balls (relative error at most 2u, u = 2^-53). Each entry is computed
from earlier entries by one dot product of at most N + 1 nonnegative terms, in any order, so it
carries a relative error at most gamma_{N+2} = (N+2)u/(1-(N+2)u) on top of the errors of its
inputs. A chain of dependencies has at most N + 2 links (at most N runs, the final sum and the
input rounding). Hence every computed P_N(k) satisfies |P~ - P| <= eps_N P with
    eps_N = (1 + gamma_{N+2})^(N+2) - 1,
an a priori bound which needs no assumption on the order of summation (BLAS and fused multiply-add
included). The a posteriori checks are the total mass defect |sum_k P~(k) - 1| and a comparison at
N = 600 with the same recursion in ball arithmetic (python-flint arb, 128 bits).
"""
import hashlib
import json
import sys
import time
from datetime import date
from pathlib import Path

import numpy as np
from flint import arb, arb_poly, ctx

ALPHA = 1.5
HERE = Path(__file__).resolve().parent
PREC = 128


def law_balls(nmax, prec=PREC):
    """f(n) and T(n) = P(X >= n) for 1 <= n <= nmax as arb balls; index 0 is 0 (f) and 1 (T)."""
    old = ctx.prec
    ctx.prec = prec
    a1 = arb(ALPHA) + 1
    z = a1.zeta()
    f = [arb(0)] + [arb(n) ** (-a1) / z for n in range(1, nmax + 1)]
    T = [arb(1)] * (nmax + 2)
    T[nmax + 1] = a1.zeta(nmax + 1) / z           # Hurwitz zeta tail, then backwards by f
    for n in range(nmax, 0, -1):
        T[n] = T[n + 1] + f[n]
    T[0] = arb(1)
    ctx.prec = old
    return f, T


def law_arrays(nmax):
    """Double-precision f and T from the ball midpoints (relative error <= 2^-52)."""
    fb, Tb = law_balls(nmax)
    f = np.array([float(x.mid()) for x in fb])
    T = np.array([float(x.mid()) for x in Tb])
    return f, T


def means():
    a1 = arb(ALPHA) + 1
    mu = float((arb(ALPHA).zeta() / a1.zeta()).mid())
    return mu


def occupation(N, f=None, T=None, fm=None, Tm=None, progress=False):
    """P_N(k), 0 <= k <= N, for a fresh plus start, in double precision.

    f, T are the plus law and fm, Tm the minus law (default: the same zeta law)."""
    if f is None:
        f, T = law_arrays(N + 1)
    if fm is None:
        fm, Tm = f, T
    B = np.zeros((N, N))                  # B[m, k] for k + m <= N - 1
    P = np.zeros(N + 1)
    fm_rev = fm[N:0:-1].copy()            # fm_rev[i] = f_-(N - i)
    t0 = time.time()
    for m in range(N):
        n = N - m                         # admissible k are 0..n-1
        if m == 0:
            a = np.zeros(n)
            a[0] = 1.0
        else:
            # A[m][k] = sum_{l=1}^{m} f_-(l) B[m-l][k] ; coefficients f_-(m), ..., f_-(1) on rows 0..m-1
            a = fm_rev[N - m:] @ B[:m, :n]
        # censored final plus run: plus count N - m, run length N - k - m = n - k
        P[N - m] += a @ T[n:0:-1]
        b = np.convolve(a, f[:n])[:n]     # f[0] = 0, so b[k] = sum_{l>=1} f_+(l) a[k-l]
        B[m, :n] = b
        # censored final minus run of length n - k, plus count k
        P[:n] += b * Tm[n:0:-1]
        if progress and m % 500 == 0:
            print(f"  m={m} elapsed {time.time() - t0:.1f}s", flush=True)
    return P


def coeff_list(poly, n):
    c = poly.coeffs()
    return [c[k] if k < len(c) else arb(0) for k in range(n)]


def occupation_arb(N, prec=PREC):
    """The same recursion in ball arithmetic. Returns a list of arb balls P_N(k)."""
    old = ctx.prec
    ctx.prec = prec
    fb, Tb = law_balls(N + 1, prec)
    fpoly = arb_poly(fb[:N])              # coefficient l is f(l), f(0) = 0
    Bs = []
    P = [arb(0)] * (N + 1)
    for m in range(N):
        n = N - m
        if m == 0:
            apoly = arb_poly([1])
        else:
            apoly = arb_poly([0])
            for l in range(1, m + 1):
                apoly += Bs[m - l] * fb[l]
            apoly = apoly.truncate(n)
        a = coeff_list(apoly, n)
        s = arb(0)
        for k in range(n):
            s += a[k] * Tb[n - k]
        P[N - m] += s
        bpoly = (apoly * fpoly).truncate(n)
        Bs.append(bpoly)
        b = coeff_list(bpoly, n)
        for k in range(n):
            P[k] += b[k] * Tb[n - k]
    ctx.prec = old
    return P


def apriori_bound(N):
    u = 2.0 ** -53
    g = (N + 2) * u / (1 - (N + 2) * u)
    return float(np.expm1((N + 2) * np.log1p(g)))


def renewal(f, J):
    """u(j), v(j) = sum_m m f^{*m}(j) for 0 <= j <= J, in double precision (nonnegative sums)."""
    u = np.zeros(J + 1)
    u[0] = 1.0
    for j in range(1, J + 1):
        u[j] = np.dot(f[1:j + 1], u[j - 1::-1])
    v = np.convolve(u, u)[:J + 1] - u     # V = U(U - 1)
    v[0] = 0.0
    return u, v


def coefficient_C(u, v, mu_plus, alpha_plus=ALPHA):
    """C(j) of Theorem thm:second-order, for 0 <= j <= len(u) - 1."""
    J = len(u) - 1
    j = np.arange(J + 1)
    green = 1.0 + mu_plus * u             # 1 + mu_+ u_-(i)
    green[0] = 1.0 + mu_plus              # u(0) = 1
    # sum_{i=0}^{j-1} u(i) (1 + mu_+ u(j-i)) = (u * green)(j) - u(j) green(0)
    conv = np.convolve(u, green)[:J + 1] - u * green[0]
    return alpha_plus * (j * u + mu_plus * v + conv)


def sha256_of(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 5000
    mu = means()
    s = 2 * mu
    t0 = time.time()
    f, T = law_arrays(N + 1)
    P = occupation(N, f, T, progress=True)
    runtime = time.time() - t0
    mass_defect = float(abs(P.sum() - 1.0))
    eps = apriori_bound(N)
    print(f"N={N}: runtime {runtime:.1f}s, mass defect {mass_defect:.3e}, a priori bound {eps:.3e}")

    # ball-arithmetic comparison at N = 600
    Nc = 600
    t1 = time.time()
    Pd = occupation(Nc)
    Pb = occupation_arb(Nc)
    tb = time.time() - t1
    rel = []
    rad = []
    contained = True
    eps_c = apriori_bound(Nc)
    for k in range(Nc + 1):
        mid = float(Pb[k].mid())
        r = float(Pb[k].rad())
        if mid == 0.0:
            if Pd[k] != 0.0:
                contained = False
            continue
        rel.append(abs(Pd[k] - mid) / mid)
        rad.append(r / mid)
        if abs(Pd[k] - mid) > r + eps_c * mid:
            contained = False
    cmp = {"N": Nc, "precision_bits": PREC, "max_rel_dev_double_vs_ball": max(rel),
           "max_rel_ball_radius": max(rad), "a_priori_bound_N600": apriori_bound(Nc),
           "double_within_ball_plus_apriori": contained, "runtime_s": tb,
           "mass_defect_double": float(abs(Pd.sum() - 1.0))}
    print("ball comparison:", cmp)

    out = {
        "header": {
            "script": "certify_atlas.py",
            "script_sha256": sha256_of(__file__),
            "date": date.today().isoformat(),
            "model": "zeta law f(n)=n^(-alpha-1)/zeta(alpha+1) for both signs, alpha_+=alpha_-=1.5, fresh plus start",
            "method": "run recursion of Proposition prop:final-run, double precision, O(N^3)",
        },
        "N": N, "alpha": ALPHA, "mu": mu, "s": s, "p": 0.5,
        "runtime_s": runtime,
        "mass_defect": mass_defect,
        "a_priori_relative_bound": eps,
        "ball_check": cmp,
        "P": [float(x) for x in P],
    }
    path = HERE / "data" / f"atlas_N{N}.json"
    path.write_text(json.dumps(out, indent=1))
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
