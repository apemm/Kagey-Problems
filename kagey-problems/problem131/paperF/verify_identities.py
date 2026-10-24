"""Exact brute-force check of the identities of Section 2 of Paper F (problem131_levy.tex).

All arithmetic is in exact rationals (fractions.Fraction). Two pairs of run laws with finite
support, different for the two signs, and one general preparation (both signs, atoms beyond the
horizon) are used. The law of the plus count is computed in two independent ways that use none of
the identities:
  (S) the sum over all 2^N sign strings of length N of the probability of the string, where the
      first run has the preparation law censored by Q, the inner runs have mass f and the last run
      is censored by T (this is the model of Section 2.1 read literally), for N <= 12;
  (H) the slot-by-slot Markov chain with state (plus count, sign, age of the current run) and
      hazard f(a)/T(a), for any N (used for the Green identity, where m runs to 23).
(S) and (H) are compared for N <= 12 first.

Checks (statement labels of problem131_levy.tex):
  eq:kernel-sums          the three kernel sums, k <= 15
  eq:kappa                the boundary kernels for a fresh plus and a fresh minus start, j <= 8
  prop:fresh-identity     fresh-plus and fresh-minus identities and their endpoint values, N <= 12
  prop:first-run          the first-run decomposition for the general preparation, N <= 12
  eq:run-sum              the final-run identity in the run form of Section sec:verify, with the
                          recursion eq:run-recursion, N <= 12,
                          and the definitions of a_t, b_t by brute force for t <= 11
  prop:final-run          the explicit form (eq:final-explicit), N <= 12
  lem:green               the Green identity for both signs, b <= 3
  lem:counting            the counting lemma: run count, pigeonhole and the bound
                          C(j+1,2) T_+(L)^2, both fresh starts, N <= 12, j <= 3, all L
  eq:cover, eq:cover-v, eq:conv-v, eq:Cj
                          the renewal identities of Section 6.2 and the two forms of C(j), j <= 15
  thm:inverse(a)          the renewal inversion u -> f, j <= 15

Run from the paper folder:  py -I verify_identities.py
Output: data/verify_identities_output.txt (with the sha256 of this script and the date).
Exit status 1 if any check fails.
"""
import hashlib
import platform
import sys
import time
from collections import defaultdict
from datetime import date
from fractions import Fraction as Fr
from itertools import product
from math import comb
from pathlib import Path

HERE = Path(__file__).resolve().parent
NMAX = 12
LINES = []


def log(msg=""):
    print(msg, flush=True)
    LINES.append(msg)


# ---------------------------------------------------------------- laws and preparation
LAWS = [
    ({1: Fr(1, 2), 2: Fr(1, 3), 3: Fr(1, 6)},
     {1: Fr(1, 5), 2: Fr(2, 5), 4: Fr(2, 5)}),
    ({1: Fr(3, 7), 2: Fr(1, 7), 3: Fr(1, 7), 5: Fr(2, 7)},
     {1: Fr(1, 9), 2: Fr(5, 9), 3: Fr(1, 9), 6: Fr(2, 9)}),
]
# general preparation: nu[sign][d] = P(Sigma = sign, D = d); atoms at 13, 15, 20 lie beyond N = 12
PREP = {'+': {1: Fr(1, 10), 3: Fr(1, 20), 7: Fr(1, 10), 13: Fr(1, 10), 20: Fr(1, 10)},
        '-': {2: Fr(1, 10), 4: Fr(1, 5), 9: Fr(1, 10), 15: Fr(3, 20)}}
OPP = {'+': '-', '-': '+'}
for a, b in LAWS:
    assert sum(a.values()) == 1 and sum(b.values()) == 1
assert sum(sum(v.values()) for v in PREP.values()) == 1


def fv(f, n):
    return f.get(n, Fr(0))


def Tv(f, n):
    """T(n) = P(X >= n) for n >= 1, extended by zero to n <= 0 (Section 2.1)."""
    return sum(v for k, v in f.items() if k >= n) if n >= 1 else Fr(0)


def Qv(nu, sg, n):
    return sum(v for d, v in nu[sg].items() if d >= n)


def fresh(sg, F):
    return {sg: dict(F[sg]), OPP[sg]: {}}


def runs(s):
    out, i = [], 0
    while i < len(s):
        j = i
        while j < len(s) and s[j] == s[i]:
            j += 1
        out.append((s[i], j - i))
        i = j
    return out


# ---------------------------------------------------------------- brute force (S): strings
def prob_string(s, F, nu):
    rr = runs(s)
    sg, r = rr[0]
    if len(rr) == 1:
        return Qv(nu, sg, r)                  # first run covers the whole string
    p = nu[sg].get(r, Fr(0))                  # first run is complete
    for sg, r in rr[1:-1]:
        p *= fv(F[sg], r)
    sg, r = rr[-1]
    return p * Tv(F[sg], r)                   # last run censored


CACHE = {}


def law_S(N, F, nu, key):
    if (key, N) not in CACHE:
        P = [Fr(0)] * (N + 1)
        for s in product('+-', repeat=N):
            P[s.count('+')] += prob_string(s, F, nu)
        CACHE[(key, N)] = P
    return CACHE[(key, N)]


# ---------------------------------------------------------------- brute force (H): hazard chain
def law_H_all(Nmax, F, sg0):
    """Fresh start of sign sg0. Returns [P_1, ..., P_Nmax] (index n -> list of length n+1)."""
    d = defaultdict(Fr)
    d[(1 if sg0 == '+' else 0, sg0, 1)] = Fr(1)
    out = {}
    for n in range(1, Nmax + 1):
        if n > 1:
            nd = defaultdict(Fr)
            for (k, sg, a), pr in d.items():
                f = F[sg]
                h = fv(f, a) / Tv(f, a)       # T(a) > 0 on reachable states
                ns = OPP[sg]
                if h:
                    nd[(k + (ns == '+'), ns, 1)] += pr * h
                if h != 1:
                    nd[(k + (sg == '+'), sg, a + 1)] += pr * (1 - h)
            d = nd
        P = [Fr(0)] * (n + 1)
        for (k, sg, a), pr in d.items():
            P[k] += pr
        out[n] = P
    return out


# ---------------------------------------------------------------- kernels
def conv(a, b, M):
    c = [Fr(0)] * (M + 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b[:M + 1 - i]):
                c[i + j] += x * y
    return c


def kernels(f, M):
    fvec = [Fr(0)] + [fv(f, n) for n in range(1, M + 1)]
    Tvec = [Fr(0)] + [Tv(f, n) for n in range(1, M + 1)]
    u = [[Fr(1)] + [Fr(0)] * M]               # u[m] = f^{*m}
    for m in range(1, M + 2):
        u.append(conv(u[-1], fvec, M))
    q = [None] + [conv(Tvec, u[m - 1], M) for m in range(1, M + 2)]
    ren = [sum(u[m][k] for m in range(0, M + 2)) for k in range(M + 1)]   # u(k), u(0) = 1
    v = [sum(m * u[m][k] for m in range(0, M + 2)) for k in range(M + 1)]  # v(k)
    return dict(f=fvec, T=Tvec, uK=u, qK=q, u=ren, v=v)


# ---------------------------------------------------------------- bookkeeping
RESULTS = {}


def chk(group, cond, detail=""):
    n, bad, first = RESULTS.get(group, (0, 0, None))
    if not cond and first is None:
        first = detail
    RESULTS[group] = (n + 1, bad + (0 if cond else 1), first)


def report_group(group):
    n, bad, first = RESULTS[group]
    status = "PASS" if bad == 0 else "FAIL"
    msg = f"{status}  {group}: {n} cases"
    if bad:
        msg += f", {bad} failed (first: {first})"
    log(msg)
    return bad == 0


def main():
    t_start = time.time()
    log("verify_identities.py: exact brute-force check of the identities of Section 2")
    for li, (fp, fm) in enumerate(LAWS):
        tag = f"law pair {li + 1}"
        log(f"\n--- {tag}: f_+ = {dict((k, str(v)) for k, v in fp.items())}, "
            f"f_- = {dict((k, str(v)) for k, v in fm.items())}")
        CACHE.clear()
        F = {'+': fp, '-': fm}
        M = 16
        K = {'+': kernels(fp, M), '-': kernels(fm, M)}
        mu = {sg: sum(n * v for n, v in F[sg].items()) for sg in '+-'}
        groups = []

        # (S) against (H)
        H = {sg: law_H_all(24, F, sg) for sg in '+-'}
        g = f"[{tag}] strings (S) = hazard chain (H), fresh starts, N <= {NMAX}"
        for sg in '+-':
            for N in range(1, NMAX + 1):
                chk(g, law_S(N, F, fresh(sg, F), 'f' + sg) == H[sg][N], f"{sg} N={N}")
        groups.append(g)

        # eq:kernel-sums
        g = f"[{tag}] eq:kernel-sums, k <= 15"
        for sg in '+-':
            k_ = K[sg]
            for k in range(1, M):
                chk(g, sum(k_['uK'][m][k] for m in range(1, M + 1)) == k_['u'][k], f"u {sg} k={k}")
                chk(g, sum(k_['qK'][m][k] for m in range(1, M + 1)) == 1, f"q {sg} k={k}")
                chk(g, sum(k_['qK'][m + 1][k] for m in range(1, M)) == 1 - k_['T'][k], f"q1 {sg} k={k}")
        groups.append(g)

        # eq:kappa: probability that a plus run starts immediately after the j-th minus slot
        g = f"[{tag}] eq:kappa, kappa^(+)_+ = u_-, kappa^(-)_+ = u_- 1{{j>=1}}, j <= 8"
        J = 8
        for sg0 in '+-':
            # enumerate run sequences until more than J minus slots; the event at level j is
            # "a minus run (or nothing, j = 0 with plus start) ends with exactly j minus slots and a
            # plus run follows"; every complete run has weight f, so the plus lengths sum out to 1
            kap = [Fr(0)] * (J + 1)

            def walk(sign, minus, w):
                # a run of sign `sign` is about to start, `minus` minus slots so far, weight w
                if sign == '+':
                    kap[minus] += w
                    for l, pl in fp.items():  # complete plus run; the plus count does not matter
                        walk('-', minus, w * pl)
                else:
                    for l, pl in fm.items():
                        if minus + l <= J:
                            walk('+', minus + l, w * pl)
            walk(sg0, 0, Fr(1))
            um = K['-']['u']
            for j in range(J + 1):
                want = um[j] if sg0 == '+' else (um[j] if j >= 1 else Fr(0))
                chk(g, kap[j] == want, f"start {sg0} j={j}")
        groups.append(g)

        up, qp, Tp = K['+']['uK'], K['+']['qK'], K['+']['T']
        um_, qm, Tm = K['-']['uK'], K['-']['qK'], K['-']['T']
        g_fresh = f"[{tag}] prop:fresh-identity (both signs, with endpoints), N <= {NMAX}"
        g_first = f"[{tag}] prop:first-run (general preparation, with endpoints), N <= {NMAX}"
        g_final = f"[{tag}] eq:run-sum with eq:run-recursion, N <= {NMAX}"
        g_abdef = f"[{tag}] eq:run-recursion, a_t and b_t by brute force, t <= {NMAX - 1}"
        g_expl = f"[{tag}] prop:final-run (eq:final-explicit), N <= {NMAX}"
        g_count = f"[{tag}] lem:counting (runs, pigeonhole, bound C(j+1,2)T_+(L)^2), N <= {NMAX}, j <= 3"
        for N in range(1, NMAX + 1):
            Fb = {sg: law_S(N, F, fresh(sg, F), 'f' + sg) for sg in '+-'}
            for k in range(1, N):
                l = N - k
                fpk = sum(um_[m][l] * qp[m + 1][k] + up[m][k] * qm[m][l] for m in range(1, N + 1))
                fmk = sum(up[m][k] * qm[m + 1][l] + um_[m][l] * qp[m][k] for m in range(1, N + 1))
                chk(g_fresh, fpk == Fb['+'][k], f"+ N={N} k={k}")
                chk(g_fresh, fmk == Fb['-'][k], f"- N={N} k={k}")
            chk(g_fresh, Fb['+'][N] == Tp[N] and Fb['+'][0] == 0, f"+ ends N={N}")
            chk(g_fresh, Fb['-'][0] == Tm[N] and Fb['-'][N] == 0, f"- ends N={N}")

            # first-run decomposition
            Pb = law_S(N, F, PREP, 'prep')

            def Fc(sg, n, k):
                if not (0 <= k <= n):
                    return Fr(0)
                return law_S(n, F, fresh(sg, F), 'f' + sg)[k]
            Qp, Qm = Qv(PREP, '+', N), Qv(PREP, '-', N)
            for k in range(N + 1):
                val = Qp * (k == N) + Qm * (k == 0)
                val += sum(PREP['+'].get(d, 0) * Fc('-', N - d, k - d) for d in range(1, N))
                val += sum(PREP['-'].get(d, 0) * Fc('+', N - d, k) for d in range(1, N))
                chk(g_first, val == Pb[k], f"N={N} k={k}")
            chk(g_first, Pb[N] == Qp and Pb[0] == Qm, f"ends N={N}")

            # final-run identity in the run form eq:run-sum with the recursion eq:run-recursion
            A = [[Fr(0)] * (N + 2) for _ in range(N + 2)]
            B = [[Fr(0)] * (N + 2) for _ in range(N + 2)]
            A[0][0] = Fr(1)
            for t in range(1, N + 1):
                for k in range(t + 1):
                    B[t][k] = sum(A[t - l][k - l] * fv(fp, l) for l in range(1, t + 1) if k - l >= 0)
                    A[t][k] = sum(B[t - l][k] * fv(fm, l) for l in range(1, t + 1))
            for j in range(N + 1):
                val = sum(A[t][t - j] * Tv(fp, N - t) for t in range(j, N)) + \
                    sum(B[N - m][N - j] * Tv(fm, m) for m in range(1, j + 1))
                chk(g_final, val == Fb['+'][N - j], f"N={N} j={j}")
            if N <= NMAX - 1:
                t = N                          # A_t, B_t from strings of length t + 1
                Ab, Bb = [Fr(0)] * (t + 1), [Fr(0)] * (t + 1)
                for s in product('+-', repeat=t + 1):
                    if s[t - 1] != s[t]:       # a run starts at slot t + 1
                        pr = prob_string(s, F, fresh('+', F))
                        # the weight of the string up to slot t with a complete run at slot t:
                        # prob_string censors the last run (slot t+1) by T(1) = 1, as wanted
                        k = s[:t].count('+')
                        (Ab if s[t] == '+' else Bb)[k] += pr
                chk(g_abdef, Ab == A[t][:t + 1] and Bb == B[t][:t + 1], f"t={t}")

            # explicit form, eq:final-explicit
            for j in range(N):
                s1 = sum(um_[r][j] * sum(up[r][a] * Tv(fp, N - j - a) for a in range(0, N - j))
                         for r in range(0, j + 1))
                s2 = sum(Tv(fm, m) * sum(um_[r][j - m] * up[r + 1][N - j] for r in range(0, j - m + 1))
                         for m in range(1, j + 1))
                chk(g_expl, s1 + s2 == Fb['+'][N - j], f"N={N} j={j}")

            # counting lemma, fresh start of either sign, full run lengths
            for sg in '+-':
                for j in range(0, min(N, 4)):
                    tots = {L: Fr(0) for L in range(1, N + 2)}
                    for s in product('+-', repeat=N):
                        if s.count('+') != N - j or s[0] != sg:
                            continue
                        rr = runs(s)
                        npr = sum(1 for x in rr if x[0] == '+')
                        chk(g_count, s.count('-') == j, f"minus count N={N}")
                        chk(g_count, npr <= j + 1 and (sg == '+' or npr <= j), f"run count N={N} j={j}")
                        chk(g_count, max(r for x, r in rr if x == '+') * (j + 1) >= N - j, f"pigeonhole N={N}")
                        p = prob_string(s, F, fresh(sg, F))
                        if p == 0:
                            continue
                        lastsg, lastr = rr[-1]
                        for L in tots:
                            inner = sum(1 for x, r in rr[:-1] if x == '+' and r >= L)
                            if lastsg == '+':
                                # the censored last plus run has full length n >= lastr with law f(n)/T(lastr)
                                plong = Tv(fp, max(lastr, L)) / Tv(fp, lastr)
                                tots[L] += p * (plong * (inner + 1 >= 2) + (1 - plong) * (inner >= 2))
                            else:
                                tots[L] += p * (inner >= 2)
                    for L, tot in tots.items():
                        chk(g_count, tot <= comb(j + 1, 2) * Tv(fp, L) ** 2, f"bound {sg} N={N} j={j} L={L}")
        groups += [g_fresh, g_first, g_final, g_abdef, g_expl, g_count]

        # lem:green with the hazard chain, sum over m >= 1 (K_m(b) = 0 for m >= b + 1 + b Lmax)
        g = f"[{tag}] lem:green, b <= 3, both signs"
        for sg in '+-':
            Lmax = max(F[OPP[sg]])
            for b in range(1, 4):
                mmax = b + 1 + b * Lmax
                assert mmax + 1 <= 24
                tot = Fr(0)
                for m in range(b, mmax + 2):
                    P = H[sg][m]
                    tot += P[b] if sg == '+' else P[m - b]
                tail = H[sg][mmax + 1]
                chk(g, (tail[b] if sg == '+' else tail[mmax + 1 - b]) == 0, f"{sg} b={b} truncation")
                want = 1 + mu[OPP[sg]] * K[sg]['u'][b]
                chk(g, tot == want, f"{sg} b={b}: {tot} vs {want}")
        groups.append(g)

        # renewal identities of Section 6.2, the two forms of C(j), and the inversion
        g = f"[{tag}] eq:cover, eq:cover-v, eq:conv-v and the two forms of eq:Cj, j <= 15"
        u, v, Tm_ = K['-']['u'], K['-']['v'], K['-']['T']
        alpha = Fr(3, 2)                       # any number: the identity is linear in alpha_+
        for j in range(1, M):
            chk(g, sum(Tm_[m] * u[j - m] for m in range(1, j + 1)) == 1, f"cover j={j}")
            chk(g, sum(Tm_[m] * v[j - m] for m in range(1, j + 1)) == sum(u[i] for i in range(1, j)), f"cover-v j={j}")
            chk(g, sum(u[i] * u[j - i] for i in range(0, j)) == v[j], f"conv-v j={j}")
            c1 = alpha * (j * u[j] + 2 * mu['+'] * v[j] + sum(u[i] for i in range(j)))
            c2 = alpha * (j * u[j] + mu['+'] * v[j] + sum(u[i] * (1 + mu['+'] * u[j - i]) for i in range(j)))
            chk(g, c1 == c2, f"Cj j={j}")
        groups.append(g)
        g = f"[{tag}] thm:inverse(a), renewal inversion u -> f, j <= 15"
        for sg in '+-':
            u = K[sg]['u']
            finv = [Fr(0)] * M
            for j in range(1, M):
                finv[j] = u[j] - sum(finv[i] * u[j - i] for i in range(1, j))
                chk(g, finv[j] == fv(F[sg], j), f"{sg} j={j}")
        groups.append(g)

        ok = all(report_group(gr) for gr in groups)
        log(f"{tag}: {'all checks passed' if ok else 'FAILURES'}")

    bad = sum(b for _, b, _ in RESULTS.values())
    total = sum(n for n, _, _ in RESULTS.values())
    log(f"\n{len(RESULTS)} check groups, {total} cases, {bad} failures, {time.time() - t_start:.1f} s")
    log("PASS  verify_identities" if bad == 0 else "FAIL  verify_identities")
    header = [f"# script: verify_identities.py",
              f"# sha256: {hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}",
              f"# date: {date.today().isoformat()}",
              f"# python {platform.python_version()}, exact rational arithmetic (fractions)", ""]
    (HERE / "data" / "verify_identities_output.txt").write_text("\n".join(header + LINES) + "\n", encoding="utf-8")
    sys.exit(0 if bad == 0 else 1)


if __name__ == "__main__":
    main()
