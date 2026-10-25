"""Check of the calibrated attraction design, Theorem `thm:attraction` of Section `sec:cycle-tree`.

For a proper face G the field is v = c t^gamma on G and 0 elsewhere, with c = 1 and
t = exp(-1/eta). The theorem says that the threshold
    tau(G) = sup{gamma : G is the strict winner at some height h > gamma}
satisfies tau(G) <= D(G), with equality when G is a cycle, so that D(F) = max_{G in F} tau(G).
We test this with the exact finite-eta scores (|G'|-1) + t^(-h) lambda_G'(v) over all nonempty
faces G', on 11 cost matrices with 4 or 3 states (the examples ex:four-state and ex:branch-switch,
a deep singleton beside a cycle, two tied reversible pair cycles, two tied non-reversible blocks,
four random non-reversible and two random reversible matrices), 138 proper faces in all.
The matrices are built from exact rationals at t = 10^(-32) and t = 10^(-48), and the two values
must give the same thresholds. lambda_G'(v) is the smallest real eigenvalue of -Q_G' - diag(v),
found by Newton's method on its exact characteristic polynomial (attraction_core.py), started
to the left of every eigenvalue, at 60 + 2 h digits and more. gamma runs over the grid
k/2 + 1/4 and h over gamma + j/4 + 1/8, so no sampled height is within 1/8 of an integer depth
or of gamma. On this grid the theorem predicts the grid threshold D(G) - 1/4 for a cycle, a grid
threshold at most D(G) - 1/4 (or none) for a noncycle, and max_{G in F} tau(G) + 1/4 = D(F).
Depths and cycles come from attraction_core.py in exact Laurent polynomial arithmetic.

Run:  py -I verify_attraction.py   (about two minutes)
"""

import importlib.util
import os
import random
import sys
from fractions import Fraction
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("attraction_core", os.path.join(HERE, "attraction_core.py"))
core = importlib.util.module_from_spec(spec)
sys.modules["attraction_core"] = core
spec.loader.exec_module(core)
import mpmath as mp

LOG = []
DISAGREE = []


def say(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    LOG.append(s)


def name(f):
    return "{" + ",".join(str(i + 1) for i in f) + "}"


def perron(A, vmax, dps, abs_digits):
    """Smallest real eigenvalue of the Z-matrix A (Fractions); Newton from the left.

    Stops when the Newton step is below 10^(-abs_digits) in absolute value."""
    mp.mp.dps = dps
    c = [mp.mpf(x.numerator) / mp.mpf(x.denominator) for x in core._charpoly(A)]
    n = len(A)
    lam = -mp.mpf(vmax.numerator) / vmax.denominator - 1
    tol = mp.mpf(10) ** (-abs_digits)
    for _ in range(100000):
        p = c[0]
        dp = mp.mpf(0)
        for k in range(1, n + 1):
            dp = dp * lam + p
            p = p * lam + c[k]
        new = lam - p / dp
        if abs(new - lam) <= tol:
            return new
        lam = new
    raise RuntimeError("Newton did not converge")


def lambdas(V, field, texp, dps, abs_digits):
    """lambda_G(v) for all nonempty faces G; field: dict state -> Fraction value of v."""
    n = len(V)
    t = Fraction(1, 10 ** texp)
    vmax = max([Fraction(0)] + [x for x in field.values()])
    out = {}
    for G in core.all_faces(n):
        A = [[Fraction(0)] * len(G) for _ in G]
        for a, i in enumerate(G):
            for b, j in enumerate(G):
                if i != j:
                    A[a][b] = -(t ** V[i][j])
            A[a][a] = sum(t ** V[i][j] for j in range(n) if j != i) - field.get(i, Fraction(0))
        out[G] = perron(A, vmax, dps, abs_digits)
    return out


def winners_above(lam, gamma, texp, hmax):
    """Winners at h = gamma + j/4 + 1/8, j = 0, 1, ..., while h < hmax."""
    tm = mp.mpf(10) ** (-texp)
    res = []
    j = 0
    while True:
        h = gamma + Fraction(j, 4) + Fraction(1, 8)
        if h >= hmax:
            break
        tau = tm ** (-(mp.mpf(h.numerator) / h.denominator))
        w = min(lam, key=lambda G: (len(G) - 1) + tau * lam[G])
        res.append((h, w))
        j += 1
    return res


def tau_scan(V, G, texp, gmin, gmax, hmax, c=Fraction(1)):
    """Largest gamma on the grid k/2+1/4 at which G wins at some sampled h > gamma."""
    t = Fraction(1, 10 ** texp)
    dmax = max(V[i][j] for i in range(len(V)) for j in range(len(V)) if i != j)
    dps = 60 + int(texp * (2 * hmax + 10))
    best = None
    gam = Fraction(-1, 4)
    while gam < gmax:
        num, den = gam.numerator, gam.denominator
        # t = 10^-texp with texp divisible by 4 makes t^gamma rational
        assert (texp * num) % den == 0
        e = texp * num // den
        s = c * (Fraction(1, 10 ** e) if e >= 0 else Fraction(10 ** (-e)))
        lam = lambdas(V, {i: s for i in G}, texp, dps, int(texp * (hmax + 3)))
        wins = [h for h, w in winners_above(lam, gam, texp, hmax) if w == G]
        if wins:
            best = gam
        gam += Fraction(1, 2)
    return best


def check_matrix(label, V, texps=(32, 48), extra_faces=None):
    n = len(V)
    base = core.PM(core.build_A(V))
    faces = core.proper_faces(n)
    D = {f: core.depth(base, f) for f in faces}
    cyc = {f: core.is_cycle(V, base, f) for f in faces}
    dmax = max(D.values())
    hmax = Fraction(dmax + 2)
    say("== %s ==" % label)
    say("  V =", V)
    say("  cycles:", ", ".join("%s(D=%d)" % (name(f), D[f]) for f in faces if cyc[f]))
    taus = {}
    for f in faces:
        vals = [tau_scan(V, f, te, 0, dmax + 1, hmax) for te in texps]
        if vals[0] != vals[1]:
            say("  t-DISAGREEMENT on", name(f), vals)
            DISAGREE.append(name(f))
        taus[f] = vals[0]
    bad = []
    for f in faces:
        tv = taus[f]
        if cyc[f]:
            ok = tv is not None and tv == D[f] - Fraction(1, 4)
        else:
            ok = tv is None or tv <= D[f] - Fraction(1, 4)
        if not ok:
            bad.append((name(f), D[f], tv, cyc[f]))
    recon_bad = []
    for f in faces:
        sub = [taus[g] for k in range(1, len(f) + 1) for g in combinations(f, k)
               if taus[g] is not None]
        est = max(sub) + Fraction(1, 4)
        if est != D[f]:
            recon_bad.append((name(f), D[f], est))
    noncyc_wins = sum(1 for f in faces if not cyc[f] and taus[f] is not None)
    say("  faces %d, cycles %d, noncycles that win somewhere above gamma: %d"
        % (len(faces), sum(cyc.values()), noncyc_wins))
    say("  tau(G) table (grid value; cycles should read D - 1/4):")
    say("   ", "; ".join("%s D=%d tau=%s%s" % (name(f), D[f], taus[f], "*" if cyc[f] else "")
                         for f in faces))
    say("  violations of tau = D - 1/4 on cycles or tau <= D - 1/4 on noncycles:", bad)
    say("  faces where max_{G in F} tau(G) + 1/4 != D(F):", recon_bad)
    return len(bad) + len(recon_bad), len(faces)


def main():
    total_bad = 0
    total_faces = 0
    cases = []
    cases.append(("example ex:four-state, reversible 4 states",
                  [[None, 2, 3, 5], [1, None, 2, 4], [2, 2, None, 2], [4, 4, 2, None]]))
    cases.append(("example ex:branch-switch, reversible 3 states",
                  [[None, 3, 3], [5, None, 1], [5, 1, None]]))
    # deep singleton elsewhere: U = (2,2,0), H12 = 3, H13 = H23 = 5
    cases.append(("deep singleton 3 beside cycle {1,2}, reversible 3 states",
                  [[None, 1, 3], [1, None, 3], [5, 5, None]]))
    cases.append(("F1 two equal pair-cycles, tied, reversible 4 states",
                  [[None, 1, 4, 4], [1, None, 4, 4], [4, 4, None, 1], [4, 4, 1, None]]))
    cases.append(("F5 two identical non-reversible blocks, tied, 4 states",
                  [[None, 1, 5, 5], [2, None, 5, 5], [5, 5, None, 1], [5, 5, 2, None]]))
    rng = random.Random(20261024)
    for k in range(4):
        V = [[None if i == j else rng.randint(0, 4) for j in range(4)] for i in range(4)]
        cases.append(("random non-reversible 4 states #%d" % (k + 1), V))
    for k in range(2):
        U = [rng.randint(0, 3) for _ in range(4)]
        H = [[None] * 4 for _ in range(4)]
        for i in range(4):
            for j in range(i + 1, 4):
                H[i][j] = H[j][i] = max(U[i], U[j]) + rng.randint(0, 3)
        V = [[None if i == j else H[i][j] - U[i] for j in range(4)] for i in range(4)]
        cases.append(("random reversible 4 states #%d" % (k + 1), V))
    for label, V in cases:
        b, f = check_matrix(label, V)
        total_bad += b
        total_faces += f
    say("TOTAL: %d proper faces checked, %d violations" % (total_faces, total_bad))
    assert total_faces == 138 and total_bad == 0 and not DISAGREE
    say("verify_attraction: PASS")


if __name__ == "__main__":
    main()
