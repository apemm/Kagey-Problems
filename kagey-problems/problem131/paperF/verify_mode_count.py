"""The numbers of Section sec:mode-count (the exact number of modes) quoted there and in Section sec:verify.

Three run laws, each the same for both signs, with the exact law from certify_atlas.occupation (the
run recursion eq:run-recursion, fresh plus start). Since the two laws are equal, a fresh minus start
is the mirror image, and the fair start is (F(k) + F(N-k))/2.
  zeta     f(n) = n^(-5/2)/zeta(5/2), n >= 1 (Corollary cor:logconvex-three).
  runs2    f(n) = n^(-5/2)/(zeta(5/2) - 1), n >= 2 (Example ex:runs2).
  runs2_75 f(n) = n^(-12/5)/(zeta(12/5) - 1), n >= 2, tail index 7/5 (Example ex:runs2).
  mixed    f(1) = 0.6, f(2) = 0.3, f(n) = 0.1 n^(-5/2)/zeta(5/2, 3), n >= 3 (after Lemma lem:one-max).
Checks.
  1. zeta: exactly three modes, at k = 1, N/2, N (fresh plus) and k = 1, N/2, N-1 (fair start), for
     N = 2500, 3000, 3500, 4000.
  2. runs2: u(2i) > max(u(2i-1), u(2i+1)) for 1 <= i <= 6, and u decreases strictly on 12 <= j <= 10^4.
  3. runs2, fair start: exactly 15 modes, at N - j and j for j = 0, 2, ..., 12 and at N/2, for every
     N = 2500, 2600, ..., 4000, and 17, 19, 17 modes at N = 1000, 1500, 2000.
  4. mixed: u(1) = 0.6 < u(2) = 0.66, and u decreases strictly on 2 <= j <= 10^4.
  5. mixed: the fair start has exactly three modes, at k = 2, N/2, N-2, and the fresh plus start four,
     at k = 2, N/2, N-2, N, for N = 1000, 1500, 2000.
  6. runs2_75, fair start: exactly 13 modes at N = 3000 and 4000 (Example ex:runs2).
Certification. Every computed value is a sum of products of nonnegative numbers, so the relative error
bound eps_N of certify_atlas.apriori_bound applies to P_N, and eps_J to u(0..J). A sign of a
difference is certified when the relative difference exceeds 2 eps. Every mode list and every
comparison of u above is certified in this sense, and the script checks it.

Run from the paper folder:  py -I verify_mode_count.py
Output: data/verify_mode_count_output.txt (with the sha256 of this script and the date).
Exit status 1 if any check fails.
"""
import hashlib
import importlib.util
import platform
import sys
import time
from datetime import date
from pathlib import Path

import numpy as np
from mpmath import mp, mpf, zeta

HERE = Path(__file__).resolve().parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, HERE / f"{name}.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


ca = load("certify_atlas")
LINES = []
FAILS = []
J_U = 10_000


def log(msg=""):
    print(msg, flush=True)
    LINES.append(msg)


def check(name, cond, detail=""):
    log(f"{'PASS' if cond else 'FAIL'}  {name}" + (f"  ({detail})" if detail else ""))
    if not cond:
        FAILS.append(name)


def law(nmax, head, tail_mass, n0, alpha=mpf(5) / 2):
    """f(n) = head[n] for n < n0 and tail_mass n^(-alpha)/zeta(alpha, n0) for n >= n0; T(n) = P(X >= n).

    Computed with 128-bit mpmath and rounded once to double precision."""
    mp.prec = 128
    a = mpf(alpha)
    z = zeta(a, n0)
    fm = [mpf(0)] * (nmax + 1)
    for n, v in head.items():
        fm[n] = mpf(v)
    for n in range(n0, nmax + 1):
        fm[n] = mpf(tail_mass) * mpf(n) ** (-a) / z
    Tm = [mpf(1)] * (nmax + 2)
    Tm[nmax + 1] = mpf(tail_mass) * zeta(a, max(nmax + 1, n0)) / z
    for n in range(nmax, 0, -1):
        Tm[n] = Tm[n + 1] + fm[n]
    Tm[0] = mpf(1)
    return np.array([float(x) for x in fm]), np.array([float(x) for x in Tm])


LAWS = {"zeta": ({}, 1.0, 1), "runs2": ({}, 1.0, 2), "mixed": ({1: 0.6, 2: 0.3}, 0.1, 3),
        "runs2_75": ({}, 1.0, 2, mpf(12) / 5)}


def renewal_u(f, J):
    u = np.zeros(J + 1)
    u[0] = 1.0
    for j in range(1, J + 1):
        u[j] = np.dot(f[1:j + 1], u[j - 1::-1])
    return u


def modes(P):
    """Strict local maxima, endpoints included when they beat their neighbour."""
    N = len(P) - 1
    out = []
    for k in range(N + 1):
        left = P[k - 1] if k > 0 else -np.inf
        right = P[k + 1] if k < N else -np.inf
        if P[k] > left and P[k] > right:
            out.append(k)
    return out


def min_rel_gap(P):
    return float(np.min(np.abs(np.diff(P)) / np.maximum(P[1:], P[:-1])))


def laws_for(N, name):
    head, tm, n0, *alpha = LAWS[name]
    f, T = law(N + 1, head, tm, n0, *alpha)
    return f, T


def main():
    t0 = time.time()
    log("verify_mode_count.py: Section sec:mode-count")
    eps_u = ca.apriori_bound(J_U)

    # 1. zeta law, fresh plus and fair start
    ok1 = True
    for N in (2500, 3000, 3500, 4000):
        f, T = laws_for(N, "zeta")
        F = ca.occupation(N, f, T)
        P = 0.5 * (F + F[::-1])
        mF, mP = modes(F), modes(P)
        g, eps = min(min_rel_gap(F), min_rel_gap(P)), ca.apriori_bound(N)
        log(f"   zeta N={N}: fresh plus modes {mF}, fair modes {mP}, smallest relative gap {g:.2e}, bound {eps:.1e}")
        ok1 = ok1 and mF == [1, N // 2, N] and mP == [1, N // 2, N - 1] and g > 2 * eps
    check("1. zeta: three modes, fresh plus and fair, N = 2500, ..., 4000 (certified)", ok1)

    # 2. runs2: the renewal mass function
    f, T = laws_for(J_U + 1, "runs2")
    u = renewal_u(f, J_U)
    rel = np.abs(np.diff(u)) / np.maximum(u[1:], u[:-1] + 1e-300)
    peaks = all(u[2 * i] > u[2 * i - 1] and u[2 * i] > u[2 * i + 1] for i in range(1, 7))
    peaks_cert = all(rel[2 * i - 1] > 2 * eps_u and rel[2 * i] > 2 * eps_u for i in range(1, 7))
    dec = bool(np.all(np.diff(u[12:]) < 0))
    dec_cert = float(np.min(rel[12:])) > 2 * eps_u
    log("   runs2: u(0..14) = " + ", ".join(f"{x:.5f}" for x in u[:15]))
    log(f"   runs2: smallest relative decrease on 12 <= j <= {J_U}: {np.min(rel[12:]):.2e}, bound {eps_u:.1e}")
    check("2. runs2: u(2i) > u(2i +- 1) for i <= 6, u strictly decreasing on [12, 10^4] (certified)",
          peaks and peaks_cert and dec and dec_cert)

    # 3. runs2: the fair start
    ok3 = True
    expect_ends = list(range(0, 13, 2))
    for N in range(2500, 4001, 100):
        f, T = laws_for(N, "runs2")
        F = ca.occupation(N, f, T)
        P = 0.5 * (F + F[::-1])
        m, g, eps = modes(P), min_rel_gap(P), ca.apriori_bound(N)
        want = expect_ends + [N // 2] + [N - j for j in reversed(expect_ends)]
        ok = m == want and g > 2 * eps
        log(f"   runs2 fair N={N}: {len(m)} modes, at the ends j = {[k for k in m if k < N // 4]}, "
            f"smallest relative gap {g:.2e}, bound {eps:.1e}")
        ok3 = ok3 and ok
    counts = {}
    for N in (1000, 1500, 2000):
        f, T = laws_for(N, "runs2")
        F = ca.occupation(N, f, T)
        P = 0.5 * (F + F[::-1])
        counts[N] = (len(modes(P)), min_rel_gap(P) > 2 * ca.apriori_bound(N))
    log(f"   runs2 fair: number of modes at N = 1000, 1500, 2000: {[counts[N][0] for N in (1000, 1500, 2000)]}")
    ok3 = ok3 and [counts[N][0] for N in (1000, 1500, 2000)] == [17, 19, 17] and all(c[1] for c in counts.values())
    check("3. runs2 fair: 15 modes for N = 2500, 2600, ..., 4000, and 17, 19, 17 at N = 1000, 1500, 2000 (certified)", ok3)

    # 4. mixed law: the renewal mass function
    f, T = laws_for(J_U + 1, "mixed")
    u = renewal_u(f, J_U)
    rel = np.abs(np.diff(u)) / np.maximum(u[1:], u[:-1])
    ok4 = (abs(u[1] - 0.6) < 1e-12 and abs(u[2] - 0.66) < 1e-12 and u[1] < u[2] and rel[1] > 2 * eps_u
           and bool(np.all(np.diff(u[2:]) < 0)) and float(np.min(rel[2:])) > 2 * eps_u)
    log(f"   mixed: u(1), u(2), u(3) = {u[1]:.6f}, {u[2]:.6f}, {u[3]:.6f}; smallest relative decrease on "
        f"2 <= j <= {J_U}: {np.min(rel[2:]):.2e}")
    check("4. mixed: u(1) = 0.6 < u(2) = 0.66, u strictly decreasing on [2, 10^4] (certified)", ok4)

    # 5. mixed law: fair and fresh plus starts
    ok5 = True
    for N in (1000, 1500, 2000):
        f, T = laws_for(N, "mixed")
        F = ca.occupation(N, f, T)
        P = 0.5 * (F + F[::-1])
        mF, mP = modes(F), modes(P)
        g, eps = min(min_rel_gap(F), min_rel_gap(P)), ca.apriori_bound(N)
        log(f"   mixed N={N}: fair modes {mP}, fresh plus modes {mF}, smallest relative gap {g:.2e}")
        ok5 = ok5 and mP == [2, N // 2, N - 2] and mF == [2, N // 2, N - 2, N] and g > 2 * eps
    check("5. mixed: fair start three modes, fresh plus four, N = 1000, 1500, 2000 (certified)", ok5)

    # 6. index 7/5 runs >= 2 law, fair start
    ok6 = True
    for N in (3000, 4000):
        f, T = laws_for(N, "runs2_75")
        F = ca.occupation(N, f, T)
        P = 0.5 * (F + F[::-1])
        m, g, eps = modes(P), min_rel_gap(P), ca.apriori_bound(N)
        log(f"   runs2_75 fair N={N}: {len(m)} modes at {m}, smallest relative gap {g:.2e}, bound {eps:.1e}")
        ok6 = ok6 and len(m) == 13 and g > 2 * eps
    check("6. runs2 of index 7/5, fair start: 13 modes at N = 3000 and 4000 (certified)", ok6)

    log(f"\n{'PASS' if not FAILS else 'FAIL'}  verify_mode_count ({len(FAILS)} failures, {time.time() - t0:.1f} s)")
    header = ["# script: verify_mode_count.py",
              f"# sha256: {hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}",
              f"# uses certify_atlas.py sha256: {ca.sha256_of(HERE / 'certify_atlas.py')}",
              f"# date: {date.today().isoformat()}",
              f"# python {platform.python_version()}, numpy {np.__version__}", ""]
    (HERE / "data" / "verify_mode_count_output.txt").write_text("\n".join(header + LINES) + "\n",
                                                                encoding="utf-8", newline="\n")
    sys.exit(0 if not FAILS else 1)


if __name__ == "__main__":
    main()
