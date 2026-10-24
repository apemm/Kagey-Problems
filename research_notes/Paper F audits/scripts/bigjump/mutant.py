"""Check Lemma lem:giant (the giant identity) symbolically for small N.

Laws: f_+(n)=a_n, f_-(n)=b_n, and the survival functions T_+(n), T_-(n) are
either independent symbols (formal check) or 1-sum_{m<n} f(m).
rho_i(x) is computed from the A_t recursion of Prop. final-run (and checked
against the representation (rho-rep)); beta_i(x)=K^-_{i+x}(i) by brute force.
The left side E[G_lambda 1{A_N=k}] and the split (giant-split) are computed by
brute-force enumeration of run sequences.
"""
import sys
import sympy as sp
from functools import lru_cache

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
FORMAL = (len(sys.argv) > 2 and sys.argv[2] == "formal")

a = sp.symbols("a1:%d" % (NMAX + 2))
b = sp.symbols("b1:%d" % (NMAX + 2))
if FORMAL:
    TP = sp.symbols("P1:%d" % (NMAX + 2))
    TM = sp.symbols("M1:%d" % (NMAX + 2))
    def Tp(n): return sp.Integer(0) if n <= 0 else TP[n - 1]
    def Tm(n): return sp.Integer(0) if n <= 0 else TM[n - 1]
else:
    def Tp(n): return sp.Integer(0) if n <= 0 else 1 - sum(a[:n - 1])
    def Tm(n): return sp.Integer(0) if n <= 0 else 1 - sum(b[:n - 1])
def fp(n): return a[n - 1] if 1 <= n else sp.Integer(0)
def fm(n): return b[n - 1] if 1 <= n else sp.Integer(0)
f = {"+": fp, "-": fm}
T = {"+": Tp, "-": Tm}
other = {"+": "-", "-": "+"}


def enumerate_runs(N, s0):
    """Yield (prob, list of (sign, slots_in_first_N, complete?))."""
    out = []
    def rec(pos, sign, runs, prob):
        for l in range(1, N - pos + 1):
            if pos + l < N:
                rec(pos + l, other[sign], runs + [(sign, l, True)], prob * f[sign](l))
        out.append((prob * T[sign](N - pos), runs + [(sign, N - pos, False)]))
    rec(0, s0, [], sp.Integer(1))
    return out


def AB(Nt, s0):
    A = {}; B = {}
    A[(0, 0)] = sp.Integer(1 if s0 == "+" else 0)
    B[(0, 0)] = sp.Integer(1 if s0 == "-" else 0)
    for t in range(1, Nt + 1):
        for k in range(0, t + 1):
            B[(t, k)] = sp.expand(sum(A.get((t - l, k - l), 0) * fp(l) for l in range(1, t + 1)))
            A[(t, k)] = sp.expand(sum(B.get((t - l, k), 0) * fm(l) for l in range(1, t + 1)))
    return A, B


def conv_power(fun, m, x):
    # P(S_m = x) for i.i.d. lengths with mass function fun
    if m == 0:
        return sp.Integer(1 if x == 0 else 0)
    if x < m:
        return sp.Integer(0)
    return sp.expand(sum(fun(l) * conv_power(fun, m - 1, x - l) for l in range(1, x - m + 2)))


def rho_rep(s0, i, x):
    tot = 0
    for m in range(0, i + 1):
        if s0 == "+":
            tot += conv_power(fm, m, i) * conv_power(fp, m, x)
        else:
            if m >= 1:
                tot += conv_power(fm, m, i) * conv_power(fp, m - 1, x)
    return sp.expand(tot)


beta_cache = {}
def beta(i, x):
    key = (i, x)
    if key not in beta_cache:
        n = i + x
        tot = 0
        for prob, runs in enumerate_runs(n, "-"):
            minus = sum(l for (sg, l, c) in runs if sg == "-")
            if minus == i:
                tot += prob
        beta_cache[key] = sp.expand(tot)
    return beta_cache[key]


def check(N, s0):
    A, B = AB(N, s0)
    rho = lambda i, x: A.get((i + x, x), 0)
    # rho-rep check
    for i in range(0, N):
        for x in range(0, N - i):
            assert sp.expand(rho(i, x) - rho_rep(s0, i, x)) == 0, ("rho-rep", s0, i, x)
    runs = enumerate_runs(N, s0)
    nbad = 0
    for lam in range(1, N + 1):
        for j in range(0, N):
            k = N - j
            lhs = 0; pk = 0; pk_small = 0; excess = 0
            for prob, rr in runs:
                plus = sum(l for (sg, l, c) in rr if sg == "+")
                if plus != k:
                    continue
                G = sum(1 for (sg, l, c) in rr if sg == "+" and l >= lam)
                M = max([l for (sg, l, c) in rr if sg == "+"] + [0])
                lhs += G * prob; pk += prob
                if M < lam: pk_small += prob
                excess += max(G - 1, 0) * prob
            C = sum(rho(j, x) * Tp(N - j - x) for x in range(0, N - j - lam + 1))
            I = 0
            for i in range(0, j):
                for x in range(0, N):
                    for xp in range(0, N):
                        L = N - j - x - xp
                        if L >= lam:
                            I += rho(i, x) * beta(j - i + (1 if i==0 else 0), xp) * fp(L)
            d1 = sp.expand(lhs - C - I)
            d2 = sp.expand(pk - (pk_small + C + I - excess))
            if d1 != 0 or d2 != 0:
                nbad += 1
                print("MISMATCH", s0, N, lam, j, d1, d2)
    return nbad


if __name__ == "__main__":
    total = 0
    for N in range(1, NMAX + 1):
        for s0 in "+-":
            nb = check(N, s0)
            total += nb
            print("N=%d start %s: mismatches %d" % (N, s0, nb), flush=True)
    print("TOTAL mismatches", total, "formal" if FORMAL else "T=1-sum f")
