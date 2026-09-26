"""Checks for the first-order correction to thm:simplex-boundary-crossover (Paper B).

Standard library only (decimal, fractions, math). mpmath is not used.

Run:
  python -B verify_crossover_factor.py predict   formula values only, no exact S (used for the
                                                 pre-registration in data/ledger_B_crossover.md)
  python -B verify_crossover_factor.py           full run; writes data/crossover_factor_output.txt
  python -B verify_crossover_factor.py repair    audit-repair checks (psi by two methods, the l = 3
                                                 cross-term example, the B.6 leading term); writes
                                                 data/crossover_factor_repair_output.txt

Names: C0 and p below are called gamma_0 and alpha in the note B_crossover.md (renamed there on
2026-09-26 after the audit, because C_0 is also the upper end of the z-range and p is Paper B's
persistence probability).

Notation (frontier_boundary.tex): r large counts n_i (sum M), l rare counts a_j, N = M + sum a_j,
L = log N, beta_i = n_i/M, rho_j = a_j L^2/N, A = sum sqrt(beta_i), g = A^2 - 1,
K = r + l - 1, H = (r-1)/2 + 2l, p = H + 3/2, k = r + l, u = z/N (u = r/p odds), v = u/(1-u),
Y = M v, s = sum a_j/N, x_j = A^2 a_j z^2/N, xi_j = A^2 a_j Y^2/M.

Exact S_n(u) = P_N(n)/V_N is computed by three methods:
  (A) proper-run formula  sum_m Prop(m) prod_i C(n_i-1, m_i-1) u^(M-1), Prop(m) = number of
      words with m_i letters i and no two equal neighbours, from a layer-by-layer integer DP;
      evaluated in double precision (all terms positive);
  (B) refresh integral (1-u)^(N-1)/v int_0^oo e^-t prod_i B_{n_i}(vt) dt, trapezoidal rule in
      w = sqrt(t), double precision, two step sizes;
  (C) positive refresh sum (1-u)^(N-1) sum_M M! v^(M-1) [y^M] prod_i sum_m C(n_i-1,m-1) y^m/m!,
      60-digit Decimal, two cutoffs.
Brute-force enumeration of all words (N <= 10) checks (A) and (C) exactly in Fractions.
"""

import math
import sys
import time
from collections import defaultdict
from decimal import Decimal as D, getcontext
from fractions import Fraction
from itertools import product
from math import comb, factorial
from pathlib import Path

getcontext().prec = 60
PI = D("3.14159265358979323846264338327950288419716939937510582097494459")
ONE = D(1)


# ---------------------------------------------------------------- special functions (Decimal)

def phi(x):
    """Phi(x) = sum_j x^j/(j!(j+1)!) = I_1(2 sqrt x)/sqrt x."""
    term = total = D(1)
    j = 0
    while True:
        j += 1
        term = term * x / (j * (j + 1))
        total += term
        if term < total * D("1e-62") and j > 2:
            return total


def psi(x):
    """psi(x) = x Phi'(x)/Phi(x) = E[J], P(J=m) proportional to x^m/(m!(m+1)!)."""
    term = total = D(1)
    first = D(0)
    j = 0
    while True:
        j += 1
        term = term * x / (j * (j + 1))
        total += term
        first += j * term
        if term < total * D("1e-62") and j > 2:
            return first / total


# ---------------------------------------------------------------- constants and profiles

class Case:
    def __init__(self, large, rare, label=""):
        self.large = tuple(large)
        self.rare = tuple(rare)
        self.counts = self.large + self.rare
        self.N = sum(self.counts)
        self.M = sum(self.large)
        self.r = len(self.large)
        self.l = len(self.rare)
        self.k = self.r + self.l
        self.label = label
        N, M = D(self.N), D(self.M)
        self.L = N.ln()
        self.beta = [D(n) / M for n in self.large]
        self.A = sum(b.sqrt() for b in self.beta)
        self.A2 = self.A * self.A
        self.g = self.A2 - 1
        self.K = self.r + self.l - 1
        self.H = D(self.r - 1) / 2 + 2 * self.l
        self.p = self.H + D(3) / 2
        prodbeta = ONE
        for b in self.beta:
            prodbeta *= b
        self.logDr = ((D(self.r) / 2 + 1) * self.A.ln() - D("0.75") * prodbeta.ln()
                      - D(self.r - 1) / 2 * (4 * PI).ln())
        self.C0 = ((self.p * self.p - self.p) / (4 * self.A2)
                   - D(3) / (16 * self.A) * sum(ONE / b.sqrt() for b in self.beta))
        self.kappa = self.A2 * (1 - D(self.k) / 2) - D(1) / 2
        self.rho = [D(a) * self.L ** 2 / N for a in self.rare]
        self.s = D(sum(self.rare)) / N

    # --- the theorem's profile and the corrections, all as logarithms
    def logP0(self, z):
        N = D(self.N)
        x = [self.A2 * a * z * z / N for a in self.rare]
        return (self.logDr + 2 * self.l * self.A.ln() + self.H * z.ln() + self.g * z
                - self.K * N.ln() + sum(phi(xx).ln() for xx in x))

    def E1(self, z):
        N = D(self.N)
        x = [self.A2 * a * z * z / N for a in self.rare]
        ps = [psi(xx) for xx in x]
        cross = sum(ps[i] * ps[j] for i in range(len(ps)) for j in range(i + 1, len(ps)))
        return (-(self.g / self.A2) * sum(x) + self.H / self.A2 * sum(ps)
                + 2 / self.A2 * cross + self.C0)

    def logPold(self, z):
        return self.logP0(z) - self.g * z * self.s

    def logPN1(self, z):
        return self.logP0(z) + self.E1(z) / z

    def logPN1k(self, z):
        return self.logPN1(z) + self.kappa * z * z / D(self.N)

    def logPM0(self, z):
        N, M = D(self.N), D(self.M)
        u = z / N
        v = u / (1 - u)
        Y = M * v
        xi = [self.A2 * a * Y * Y / M for a in self.rare]
        return (self.logDr + 2 * self.l * self.A.ln() + self.H * Y.ln() - self.K * M.ln()
                + self.A2 * Y + (N - 1) * (1 - u).ln() + sum(phi(t).ln() for t in xi))

    def Theta(self, z):
        N, M = D(self.N), D(self.M)
        u = z / N
        v = u / (1 - u)
        Y = M * v
        xi = [self.A2 * a * Y * Y / M for a in self.rare]
        ps = [psi(t) for t in xi]
        cross = sum(ps[i] * ps[j] for i in range(len(ps)) for j in range(i + 1, len(ps)))
        return sum(xi) / self.A2 + self.H / self.A2 * sum(ps) + 2 / self.A2 * cross + self.C0

    def logPMa(self, z):
        """M-form with Theta/Y but without the majorant factor exp(-(k/2) A^2 Y v)."""
        N, M = D(self.N), D(self.M)
        Y = M * (z / N) / (1 - z / N)
        return self.logPM0(z) + self.Theta(z) / Y

    def logPM1(self, z):
        N, M = D(self.N), D(self.M)
        u = z / N
        v = u / (1 - u)
        Y = M * v
        return (self.logPM0(z) + self.Theta(z) / Y - D(self.k) / 2 * self.A2 * Y * v)

    def theorem_root(self):
        """Right side of eq. (simplex-boundary-root) without its error term."""
        c = D(self.K) / self.g
        const = (self.logDr + 2 * self.l * self.A.ln() + self.H * c.ln()
                 + sum(phi(self.A2 * c * c * rh).ln() for rh in self.rho))
        return c * self.L - self.H / self.g * self.L.ln() - const / self.g


def make_case(N, rhos, weights, label=""):
    L = math.log(N)
    rare = [max(1, round(rh * N / L ** 2)) for rh in rhos]
    M = N - sum(rare)
    large = [M * w // sum(weights) for w in weights]
    large[-1] += M - sum(large)
    return Case(large, rare, label)


# ---------------------------------------------------------------- exact S, method (C)

def positive_poly(counts, cutoff):
    """[y^M] prod_i sum_{m=1}^{n_i} C(n_i-1,m-1) y^m/m!, M <= cutoff, as Decimals."""
    total = [D(1)]
    for n in counts:
        single = [D(0)] * (cutoff + 1)
        single[1] = D(1)
        for m in range(2, min(n, cutoff) + 1):
            single[m] = single[m - 1] * (n - m + 1) / ((m - 1) * m)
        new = [D(0)] * (cutoff + 1)
        for i, ti in enumerate(total):
            if ti == 0:
                continue
            for j in range(1, cutoff + 1 - i):
                if single[j] == 0:
                    continue
                new[i + j] += ti * single[j]
        total = new
    return total


def eval_positive(N, poly, z):
    N = D(N)
    u = z / N
    v = u / (1 - u)
    acc = D(0)
    fact_v = D(1)  # M! v^(M-1), start at M = 1: 1! v^0
    for M in range(1, len(poly)):
        if M > 1:
            fact_v = fact_v * M * v
        acc += fact_v * poly[M]
    return acc * ((N - 1) * (1 - u).ln()).exp()


def cutoff_for(case, zmax):
    zf = float(zmax)
    tstar = sum(math.sqrt(n * zf / case.N) for n in case.counts) ** 2
    return int(3 * tstar + 20 * math.sqrt(tstar) + 60)


def exact_C(case, z, extra=60):
    cut = cutoff_for(case, z)
    p1 = positive_poly(case.counts, cut)
    p2 = positive_poly(case.counts, cut + extra)
    s1, s2 = eval_positive(case.N, p1, z), eval_positive(case.N, p2, z)
    return s2, abs(s1 / s2 - 1)


# ---------------------------------------------------------------- exact S, method (B)

def logB(n, w):
    """log B_n(w), B_n(w) = sum_{m=1}^n C(n-1,m-1) w^m/m!, double precision."""
    term = total = w
    m = 1
    peak = math.sqrt(n * w) + 2
    while m < n:
        term *= (n - m) * w / (m * (m + 1))
        m += 1
        total += term
        if m > peak and term < 1e-18 * total:
            break
    return math.log(total)


def exact_B(case, z, h=0.04, span=12.0):
    N = case.N
    u = float(z) / N
    v = u / (1 - u)
    wstar = sum(math.sqrt(n * v) for n in case.counts)
    lo = max(h, wstar - span)
    nodes = int((wstar + span - lo) / h) + 1
    logs = []
    for i in range(nodes):
        w = lo + i * h
        t = w * w
        val = math.log(2 * w) - t + sum(logB(n, v * t) for n in case.counts)
        logs.append(val)
    mx = max(logs)
    integral = h * sum(math.exp(x - mx) for x in logs)
    # w in (0, lo) is included only when lo = h (then the endpoint term at w=0 is 0).
    return (N - 1) * math.log1p(-u) - math.log(v) + mx + math.log(integral)


def exact_B_checked(case, z):
    a = exact_B(case, z, 0.04, 12.0)
    b = exact_B(case, z, 0.08, 16.0)
    return a, abs(a - b)


# ---------------------------------------------------------------- exact S, method (A)

def proper_counts_3(Mmax, cap):
    """Prop(m1,m2,m3) for proper words, all m_i >= 1, m1+m2+m3 <= Mmax, m3 <= cap.
    Returned as {(m1,m2,m3): float(count)}; counts are exact integers before conversion."""
    layer = {(1, 0, 0): 1, (0, 0, 1): 1, (0, 1, 2): 1}  # (m1, m3, last)
    out = {}
    for M in range(1, Mmax + 1):
        for (m1, m3, last), c in layer.items():
            m2 = M - m1 - m3
            if m1 >= 1 and m2 >= 1 and m3 >= 1:
                key = (m1, m2, m3)
                out[key] = out.get(key, 0) + c
        if M == Mmax:
            break
        new = defaultdict(int)
        for (m1, m3, last), c in layer.items():
            if last != 0:
                new[(m1 + 1, m3, 0)] += c
            if last != 1:
                new[(m1, m3, 1)] += c
            if last != 2 and m3 < cap:
                new[(m1, m3 + 1, 2)] += c
        layer = new
    return out


def log_weights(n, u, mmax):
    """log[C(n-1,m-1) u^(m-1)] for m = 1..mmax (index m), -inf beyond n."""
    out = [float("-inf")] * (mmax + 1)
    out[1] = 0.0
    lu = math.log(u)
    for m in range(2, min(n, mmax) + 1):
        out[m] = out[m - 1] + math.log(n - m + 1) - math.log(m - 1) + lu
    return out


def exact_A(case, z, prop, Mmax):
    """Proper-run formula. Returns (log S, relative mass in the top 30 layers)."""
    assert case.k == 3
    u = float(z) / case.N
    w = [log_weights(n, u, Mmax) for n in case.counts]
    logs = []
    tops = []
    for m1, m2, m3, lc in prop:
        val = lc + w[0][m1] + w[1][m2] + w[2][m3]
        logs.append(val)
        if m1 + m2 + m3 > Mmax - 30:
            tops.append(val)
    mx = max(logs)
    tot = sum(math.exp(x - mx) for x in logs)
    top = sum(math.exp(x - mx) for x in tops) / tot
    # log_weights carries u^(m_i - 1) for each color; the formula needs u^(M-1).
    return mx + math.log(tot) + (case.k - 1) * math.log(u), top


# ---------------------------------------------------------------- brute force (N <= 10)

def brute_force_checks():
    """All words on 3 or 4 letters of length N <= 10: compare exact S_n(u) at u = 1/7."""
    u = Fraction(1, 7)
    checked = 0
    small_prop = {}
    for k, Nmax in ((3, 10), (4, 7)):
        for N in range(k, Nmax + 1):
            table = defaultdict(lambda: defaultdict(int))
            for word in product(range(k), repeat=N):
                cnt = tuple(word.count(c) for c in range(k))
                if min(cnt) == 0:
                    continue
                ch = sum(1 for i in range(N - 1) if word[i] != word[i + 1])
                table[cnt][ch] += 1
            for cnt, poly in table.items():
                brute = sum(Fraction(c) * u ** j for j, c in poly.items())
                # (C) exact in Fractions
                v = u / (1 - u)
                tot = [Fraction(1)]
                for n in cnt:
                    single = [Fraction(0)] + [Fraction(comb(n - 1, m - 1), factorial(m))
                                              for m in range(1, n + 1)]
                    new = [Fraction(0)] * (len(tot) + len(single) - 1)
                    for i, a in enumerate(tot):
                        for j, b in enumerate(single):
                            new[i + j] += a * b
                    tot = new
                posC = (1 - u) ** (N - 1) * sum(factorial(M) * v ** (M - 1) * c
                                               for M, c in enumerate(tot) if M >= 1)
                assert posC == brute, (cnt, posC, brute)
                # (A) proper-run formula with Prop from an independent small DP
                if k == 3:
                    prop = small_prop.setdefault(N, proper_counts_3(N, N))
                    propA = sum(Fraction(c) * comb(cnt[0] - 1, m1 - 1)
                                * comb(cnt[1] - 1, m2 - 1) * comb(cnt[2] - 1, m3 - 1)
                                * u ** (m1 + m2 + m3 - 1)
                                for (m1, m2, m3), c in prop.items()
                                if m1 <= cnt[0] and m2 <= cnt[1] and m3 <= cnt[2])
                    assert propA == brute, (cnt, propA, brute)
                checked += 1
    return checked


# ---------------------------------------------------------------- refined lemma checks

def refined_lemma_checks(out):
    """|B_n(w)/(w Phi(nw)) - 1 + w/2| <= (3/4) w^2, and Bessel-law moments, 60 digits."""
    worst = D(0)
    for n in (1, 2, 3, 5, 10, 100, 10 ** 4):
        for w in map(D, ("0.0001", "0.01", "0.1", "0.5", "1", "2")):
            B = term = w  # terms C(n-1,m-1) w^m/m! by their ratio (n-m) w/(m(m+1))
            for m in range(1, n):
                term = term * (n - m) * w / (m * (m + 1))
                B += term
                if term < B * D("1e-70") and m * m > n * w:
                    break
            dev = abs(B / (w * phi(n * w)) - 1 + w / 2) / (w * w)
            assert dev <= D("0.75"), (n, w, dev)
            worst = max(worst, dev)
    out.append(f"[lemma] |B_n(w)/(w Phi(nw)) - 1 + w/2| / w^2 <= 0.75 at 42 points; "
               f"largest value {fmt(worst, 5)}")
    for x in map(D, ("0.01", "1", "16", "64")):
        Z = phi(x)
        term, m, m1, m2 = D(1), 0, D(0), D(0)
        while True:
            m += 1
            term = term * x / (m * (m + 1))
            m1 += m * (m + 1) * term
            m2 += m * (m - 1) * m * (m + 1) * term
            if term < D("1e-65") * Z and m > 5:
                break
        assert abs(m1 / Z - x) < D("1e-50") * (1 + x)
        assert abs(m2 / Z - x * x) < D("1e-50") * (1 + x * x)
    out.append("[lemma] E[J(J+1)] = x and E[J(J-1)J(J+1)] = x^2 at x = 0.01, 1, 16, 64 "
               "(50 digits)")


# ---------------------------------------------------------------- reporting helpers

def fmt(x, n=4):
    return f"{float(x):.{n}f}"


def predict_mode(out):
    out.append("PREDICT MODE: formula values only (no exact S computed).")
    for N, rho in ((2000, 1), (2000, 8), (20000, 8), (200000, 8), (2000000, 8)):
        c = make_case(N, [rho], [1, 1])
        z = c.L
        out.append(
            f"N={N} counts={c.counts} rho_actual={fmt(c.rho[0])} x={fmt(c.A2*c.rho[0])} "
            f"psi(x)={fmt(psi(c.A2*c.rho[0]))} E1={fmt(c.E1(z))} C0={fmt(c.C0)} "
            f"kappa={fmt(c.kappa)}")
        out.append(
            f"    PN1/P0={fmt((c.logPN1(z)-c.logP0(z)).exp())} "
            f"PN1k/P0={fmt((c.logPN1k(z)-c.logP0(z)).exp())} "
            f"PM1/P0={fmt((c.logPM1(z)-c.logP0(z)).exp())} "
            f"Pold/P0={fmt((c.logPold(z)-c.logP0(z)).exp())}")
    for rho in (1, 8):
        x = D(2) * rho
        out.append(f"limit E1 (r=2 equal, l=1, z=L, x=2rho={x}): "
                   f"{fmt(-x/2 + D('1.25')*psi(x) + D('1.125'), 6)}; "
                   f"z=2L (x=8rho): {fmt(-4*x/2 + D('1.25')*psi(4*x) + D('1.125'), 6)}")


def psi_cf(x, depth):
    """Second method for psi: psi(x) = sqrt(x) I_2(t)/I_1(t), t = 2 sqrt x, with
    I_nu/I_{nu-1} = 1/(2 nu/t + I_{nu+1}/I_nu) (from I_{nu-1} - I_{nu+1} = (2 nu/t) I_nu, which
    follows from the power series by shifting the summation index), evaluated backward from
    the given depth with tail 0."""
    rx = x.sqrt()
    t = 2 * rx
    f = D(0)
    for nu in range(depth, 1, -1):
        f = ONE / (2 * nu / t + f)
    return rx * f


def repair_mode(out):
    """Checks for the audit repair (registered in data/ledger_B_crossover.md, 2026-09-26)."""
    t0 = time.time()
    out.append("REPAIR MODE (audit repair, 2026-09-26). No exact S is computed here.")
    out.append("psi by (a) series x Phi'/Phi and (b) continued fraction at depths 300 and 600")
    out.append("x        psi(a)                          psi(b,600)                      "
               "|a-b|    |b300-b600|")
    pa, pb = {}, {}
    for xs in ("0.5", "1", "2", "4", "6", "8", "16", "32", "64", "256"):
        x = D(xs)
        a = psi(x)
        b3, b6 = psi_cf(x, 300), psi_cf(x, 600)
        pa[xs], pb[xs] = a, b6
        out.append(f"{xs:<8s} {str(+a)[:30]:<31s} {str(+b6)[:30]:<31s} "
                   f"{float(abs(a-b6)):.1e}  {float(abs(b3-b6)):.1e}")
    out.append("")
    out.append("X1. r = 2 equal (A^2 = 2, g = 1), l = 3 equal x, H = 13/2:")
    out.append("    z E - gamma_0 = (1/2)[-3x + (39/2) psi(x) + 6 psi(x)^2]; first term -3x/2")
    out.append("x      first term   zE-gamma_0 (a)   zE-gamma_0 (b)")
    for xs in ("16", "64", "256"):
        x = D(xs)
        vals = [(-3 * x + D(39) / 2 * ps + 6 * ps * ps) / 2 for ps in (pa[xs], pb[xs])]
        out.append(f"{xs:<6s} {fmt(-3*x/2, 1):>10s}   {fmt(vals[0], 4):>14s}   "
                   f"{fmt(vals[1], 4):>14s}")
    out.append("")
    out.append("X2. l = 2, r = 2 equal, rho = (1, 3), z = L: H - K = 3/2, x = (2, 6)")
    for tag, P in (("a", pa), ("b", pb)):
        proved = -(1 + 3) * (D(3) / 2 + P["2"] + P["6"])
        perj = -(1 * (D(3) / 2 + P["2"]) + 3 * (D(3) / 2 + P["6"]))
        out.append(f"    ({tag}) -(sum rho)(H-K+sum psi) = {fmt(proved, 4)}   "
                   f"per-j form -sum rho_j(H-K+psi_j) = {fmt(perj, 4)}")
    out.append("    compare (full-run output, section 2, l = 2 family): "
               "d2 - dM = -15.495 (1e12), -15.642 (1e16)")
    out.append("")
    out.append("X3. l = 1, r = 2 equal, z = L: -rho(H - K + psi(2 rho)), H - K = 1/2")
    out.append("rho    (a)          (b)          |a-b|")
    for rs, xs in (("0.25", "0.5"), ("0.5", "1"), ("1", "2"), ("2", "4"), ("4", "8"),
                   ("8", "16"), ("16", "32"), ("32", "64")):
        rho = D(rs)
        ha = -rho * (D(1) / 2 + pa[xs])
        hb = -rho * (D(1) / 2 + pb[xs])
        out.append(f"{rs:<6s} {fmt(ha, 4):>10s}   {fmt(hb, 4):>10s}   {float(abs(ha-hb)):.1e}")
    out.append("")
    out.append(f"repair mode time {time.time()-t0:.2f} s")


def main():
    t0 = time.time()
    out = []
    if len(sys.argv) > 1 and sys.argv[1] == "predict":
        predict_mode(out)
        print("\n".join(out))
        return
    if len(sys.argv) > 1 and sys.argv[1] == "repair":
        repair_mode(out)
        text = "\n".join(out) + "\n"
        path = Path(__file__).resolve().parent / "data" / "crossover_factor_repair_output.txt"
        path.write_text(text, encoding="utf-8")
        print(text)
        return

    out.append("verify_crossover_factor.py  (Problem 131, Paper B, thm:simplex-boundary-crossover)")
    out.append("All exact values of S: (A) proper-run formula, (B) refresh integral quadrature,")
    out.append("(C) positive refresh sum in 60-digit Decimal. Ratios are exact S / profile.")
    out.append("")

    refined_lemma_checks(out)
    nb = brute_force_checks()
    out.append(f"[brute force] {nb} count vectors (3 letters N<=10, 4 letters N<=7): "
               f"(C) and (A) equal the enumerated S_n(1/7) exactly.")
    out.append("")

    # proper-run table for (A)
    MMAX, CAP = 170, 40
    prop = [(m1, m2, m3, math.log(c))
            for (m1, m2, m3), c in proper_counts_3(MMAX, CAP).items()]
    out.append(f"[A] proper-word counts computed for M <= {MMAX}, rare runs <= {CAP}: "
               f"{len(prop)} triples ({time.time()-t0:.1f} s)")
    out.append("")

    # ---------------- 1. the remark's five points
    out.append("== 1. The remark's points: two equal large counts, one rare count, z = log N ==")
    out.append("a = round(rho N/L^2), n1 = floor((N-a)/2), n2 = N-a-n1; profile uses actual rho.")
    hdr = ("N        counts                 rho_act  S/P0(A)  S/P0(B)  S/P0(C)  maxreldiff "
           "S/Pold  S/PN1  S/PN1k  S/PM0  S/PMa  S/PM1")
    out.append(hdr)
    for N, rho in ((2000, 1), (2000, 8), (20000, 8), (200000, 8), (2000000, 8)):
        for shift in (0, -1, 1):
            c = make_case(N, [rho], [1, 1])
            if shift:
                a = c.rare[0] + shift
                M = N - a
                c = Case([M // 2, M - M // 2], [a])
            z = c.L
            lA, topA = exact_A(c, z, prop, MMAX)
            lB, errB = exact_B_checked(c, z)
            SC, errC = exact_C(c, z)
            lC = SC.ln()
            diff = max(abs(lA - float(lC)), abs(lB - float(lC)))
            lp0 = c.logP0(z)
            row = (f"{N:<8d} {str(c.counts):<22s} {fmt(c.rho[0],3):>7s}  "
                   f"{math.exp(lA-float(lp0)):.4f}   {math.exp(lB-float(lp0)):.4f}   "
                   f"{(lC-lp0).exp():.4f}   {diff:.1e}   "
                   f"{fmt((lC-c.logPold(z)).exp())}  {fmt((lC-c.logPN1(z)).exp())}  "
                   f"{fmt((lC-c.logPN1k(z)).exp())}  {fmt((lC-c.logPM0(z)).exp())}  "
                   f"{fmt((lC-c.logPMa(z)).exp())}  {fmt((lC-c.logPM1(z)).exp())}")
            if shift:
                row += "   (a shifted by %+d)" % shift
            out.append(row)
            assert diff < 1e-9 and topA < 1e-20 and errB < 1e-9 and errC < D("1e-40")
    out.append("")

    # ---------------- 2. asymptotic sequences
    out.append("== 2. First-order coefficient: d0 = z log(S/P0) -> E1(x); d2 = z^2 log(S/PN1k), "
               "dM = z^2 log(S/PM1) bounded ==")
    out.append("(z(d0-E1) = z^2 log(S/(P0 exp(E1/z))) differs from d2 only by kappa z^4/N.)")
    families = [
        ("r=2 equal, l=1, rho=1, z=L", [1], [1, 1], 1),
        ("r=2 equal, l=1, rho=8, z=L", [8], [1, 1], 1),
        ("r=2 equal, l=1, rho=1, z=2L", [1], [1, 1], 2),
        ("r=2 equal, l=1, rho=8, z=2L", [8], [1, 1], 2),
        ("r=2 equal, l=2, rho=(1,3), z=L", [1, 3], [1, 1], 1),
        ("r=3 beta=(1,2,3)/6, l=1, rho=2, z=L", [2], [1, 2, 3], 1),
        ("r=2 equal, l=1, rho=0.25, z=L", [D("0.25")], [1, 1], 1),
    ]
    for name, rhos, weights, zmul in families:
        out.append(f"-- {name}")
        out.append("N        z        E1(x)     d0=z*log(S/P0)  d0-E1    z*(d0-E1)  "
                   "d2=z^2log(S/PN1k)  dM=z^2log(S/PM1)  |B-C|    |A-C|")
        for e in range(3, 17):
            N = 10 ** e
            c = make_case(N, [float(r) for r in rhos], weights)
            z = zmul * c.L
            SC, errC = exact_C(c, z)
            lC = SC.ln()
            lB, errB = exact_B_checked(c, z)
            dBC = abs(lB - float(lC))
            dAC = float("nan")
            if c.k == 3 and e <= 8:
                lA, topA = exact_A(c, z, prop, MMAX)
                dAC = abs(lA - float(lC))
                assert topA < 1e-12, (name, N, topA)
            assert dBC < 1e-9 and errC < D("1e-40") and errB < 1e-9, (name, N, dBC, errC, errB)
            E1 = c.E1(z)
            d0 = z * (lC - c.logP0(z))
            d2 = z * z * (lC - c.logPN1k(z))
            dM = z * z * (lC - c.logPM1(z))
            out.append(f"1e{e:<6d} {fmt(z,3):>7s}  {fmt(E1,4):>8s}  {fmt(d0,4):>12s}  "
                       f"{fmt(d0-E1,4):>8s}  {fmt(z*(d0-E1),3):>9s}  {fmt(d2,3):>14s}  "
                       f"{fmt(dM,3):>14s}     {dBC:.1e}  {dAC:.1e}")
        out.append("")

    # ---------------- 3. roots
    out.append("== 3. Crossing z_N = N u_N (S = 1) vs the theorem's root formula and the roots "
               "of the corrected profiles ==")
    out.append("N        rho  z_N(C)        z_N(B)        thm formula   root P0       root PN1      "
               "root PN1k     root PMa      root PM1")
    for rho in (1, 8):
        for e in (4, 6, 8, 12):
            N = 10 ** e
            c = make_case(N, [rho], [1, 1])
            zmax = 4 * c.L
            cut = cutoff_for(c, zmax)
            poly = positive_poly(c.counts, cut)

            def bisect(f, lo, hi, it=80):
                flo = f(lo)
                for _ in range(it):
                    mid = (lo + hi) / 2
                    fm = f(mid)
                    if (fm < 0) == (flo < 0):
                        lo, flo = mid, fm
                    else:
                        hi = mid
                return (lo + hi) / 2

            zC = bisect(lambda zz: eval_positive(c.N, poly, zz).ln(), c.L / 2, zmax)
            zB = bisect(lambda zz: exact_B(c, D(zz)), float(c.L) / 2, float(zmax), 60)
            z0 = bisect(lambda zz: c.logP0(zz), c.L / 2, zmax)
            zn = bisect(lambda zz: c.logPN1(zz), c.L / 2, zmax)
            z1 = bisect(lambda zz: c.logPN1k(zz), c.L / 2, zmax)
            zM = bisect(lambda zz: c.logPM1(zz), c.L / 2, zmax)
            za = bisect(lambda zz: c.logPMa(zz), c.L / 2, zmax)
            zt = c.theorem_root()
            out.append(f"1e{e:<6d} {rho:<4d} {fmt(zC,6)}   {zB:.6f}   {fmt(zt,6)}   "
                       f"{fmt(z0,6)}   {fmt(zn,6)}   {fmt(z1,6)}   {fmt(za,6)}   {fmt(zM,6)}")
            assert abs(float(zC) - zB) < 1e-7
    out.append("")

    # ---------------- 4. R-dependence of the second-order constants
    out.append("== 4. Second-order constants at N = 1e12, z = L, r = 2 equal, l = 1 ==")
    out.append("c2N = z^2 log(S/PN1k), c2M = z^2 log(S/PM1), heur = -rho(H-K+psi(A^2 rho)) "
               "(predicted value of c2N - c2M)")
    out.append("rho     E1(x)      c2N        c2M      c2N-c2M     heur     |B-C|")
    for rho in (D("0.25"), D("0.5"), 1, 2, 4, 8, 16, 32):
        c = make_case(10 ** 12, [float(rho)], [1, 1])
        z = c.L
        SC, errC = exact_C(c, z)
        lC = SC.ln()
        lB, errB = exact_B_checked(c, z)
        assert abs(lB - float(lC)) < 1e-9 and errC < D("1e-40")
        c2N = z * z * (lC - c.logPN1k(z))
        c2M = z * z * (lC - c.logPM1(z))
        heur = -c.rho[0] * (c.H - c.K + psi(c.A2 * c.rho[0]))
        out.append(f"{str(rho):<6s} {fmt(c.E1(z),4):>8s}  {fmt(c2N,3):>9s}  {fmt(c2M,3):>8s}  "
                   f"{fmt(c2N-c2M,3):>9s}  {fmt(heur,3):>8s}   {abs(lB-float(lC)):.1e}")
    out.append("")
    out.append(f"total time {time.time()-t0:.1f} s")
    text = "\n".join(out) + "\n"
    path = Path(__file__).resolve().parent / "data" / "crossover_factor_output.txt"
    path.write_text(text, encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
