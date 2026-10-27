"""Every-N counts for completely monotone (CM) run laws.

Run with `py -I cm_everyN.py [Nmax] [nlaws] [seed]`.

A CM law is a mixture of geometric laws, f(n) = int th^{n-1} (1 - th) mu(d th).  We draw
random CM laws of three kinds: finite geometric mixtures (2 or 3 atoms, with some atoms
near 1), Sibuya(alpha) (a Beta mixture; heavy tail, infinite mean), and mixtures of a Sibuya
law with geometric atoms.  The two signs get independent laws, or the same law.  For every
N <= Nmax and the starts fair, fresh plus, fresh minus we record:
    total modes (endpoint convention), interior modes (1 <= k <= N-1), sign changes of dP.
Statements tested:
    (F3)  fair start: total modes <= 3 for every N;
    (F3s) fair start, same law for both signs: total modes <= 3 for every N;
    (I3)  fresh starts: interior modes <= 3 for every N;
    (I2)  fresh starts: interior modes <= 2 for every N.
Counts are taken with ties at relative level 1e-11 treated as plateaus; every case that
breaks a statement is re-checked in exact rational arithmetic when the law is a finite
geometric mixture with rational parameters (we draw rational parameters for that reason).
"""
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from shape_engine import Engine, sibuya, geom_mix, mix, modes, Law


def rand_law(rng, n):
    kind = rng.integers(0, 3)
    if kind == 0:
        k = int(rng.integers(2, 4))
        th = [Fr(int(rng.integers(1, 100)), 100) for _ in range(k)]
        if rng.random() < 0.7:
            th[0] = Fr(int(rng.integers(95, 100)), 100) if rng.random() < 0.5 else Fr(int(rng.integers(990, 1000)), 1000)
        wr = [int(rng.integers(1, 20)) for _ in range(k)]
        w = [Fr(x, sum(wr)) for x in wr]
        L = geom_mix([float(x) for x in w], [float(x) for x in th], n)
        L.exact = (w, th)
        return L
    if kind == 1:
        a = float(np.round(rng.uniform(0.05, 0.95), 2))
        L = sibuya(a, n)
        L.exact = None
        return L
    a = float(np.round(rng.uniform(0.05, 0.95), 2))
    p = float(np.round(rng.uniform(0.1, 0.9), 2))
    th = float(np.round(rng.uniform(0.0, 0.99), 2))
    L = mix([sibuya(a, n), geom_mix([1.0], [th], n)], [p, 1 - p],
            "%.2f sib(%.2f) + %.2f geom(%.2f)" % (p, a, 1 - p, th))
    L.exact = None
    return L


def exact_law(wth_p, wth_m, N, start):
    """Exact P_N for finite geometric mixtures: hidden chain on (sign, component)."""
    (wp, tp), (wm, tm) = wth_p, wth_m
    # state: dict (sign, comp, k) -> prob after some steps; first step chooses component
    cur = {}
    if start in (1, 0):
        for c, (w, t) in enumerate(zip(wp, tp)):
            cur[(1, c, 1)] = cur.get((1, c, 1), 0) + w * (Fr(1, 2) if start == 0 else 1)
    if start in (-1, 0):
        for c, (w, t) in enumerate(zip(wm, tm)):
            cur[(-1, c, 0)] = cur.get((-1, c, 0), 0) + w * (Fr(1, 2) if start == 0 else 1)
    for _ in range(N - 1):
        nxt = {}
        for (s, c, k), pr in cur.items():
            t = tp[c] if s > 0 else tm[c]
            # continue the run
            key = (s, c, k + (1 if s > 0 else 0))
            nxt[key] = nxt.get(key, 0) + pr * t
            # switch sign, draw a new component
            ws, ts = (wm, tm) if s > 0 else (wp, tp)
            for c2, w2 in enumerate(ws):
                key = (-s, c2, k + (1 if -s > 0 else 0))
                nxt[key] = nxt.get(key, 0) + pr * (1 - t) * w2
        cur = nxt
    P = [Fr(0)] * (N + 1)
    for (s, c, k), pr in cur.items():
        P[k] += pr
    return P


def exact_modes(P):
    n = len(P)
    d = [P[i + 1] - P[i] for i in range(n - 1)]
    s = [(x > 0) - (x < 0) for x in d]
    blocks, a = [], 0
    for i in range(n - 1):
        if s[i] != 0:
            blocks.append((a, i))
            a = i + 1
    blocks.append((a, n - 1))
    mx = []
    for (a, b) in blocks:
        left = s[a - 1] if a > 0 else None
        right = s[b] if b < n - 1 else None
        if ((left is None) or left > 0) and ((right is None) or right < 0) and not (left is None and right is None):
            mx.append((a, b))
    return mx


if __name__ == "__main__":
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    nlaws = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    rng = np.random.default_rng(seed)
    worst = {"F3": (0, None), "F3s": (0, None), "I3": (0, None), "I2": (0, None),
             "fresh_total": (0, None), "fair_sc": (0, None)}
    breaks = []
    for it in range(nlaws):
        same = rng.random() < 0.4
        lp = rand_law(rng, Nmax + 5)
        lm = lp if same else rand_law(rng, Nmax + 5)
        E = Engine(lp, lm, Nmax)
        for N in range(2, Nmax + 1):
            for st in ("fair", "plus", "minus"):
                P = E.fair(N) if st == "fair" else E.fresh(N, 1 if st == "plus" else -1)
                mx, mn, gap = modes(P, rtol=1e-11)
                tot = len(mx)
                inter = len([1 for a, b in mx if a > 0 and b < N])
                tag = (lp.name, lm.name, N, st, [a for a, b in mx])
                if st == "fair":
                    if tot > worst["F3"][0]:
                        worst["F3"] = (tot, tag)
                    if same and tot > worst["F3s"][0]:
                        worst["F3s"] = (tot, tag)
                    d = np.diff(P)
                    sc = int(np.sum(np.sign(d[d != 0])[1:] != np.sign(d[d != 0])[:-1]))
                    if sc > worst["fair_sc"][0]:
                        worst["fair_sc"] = (sc, tag)
                    if tot > 3:
                        breaks.append(("F3", tag, gap, lp, lm))
                else:
                    if inter > worst["I3"][0]:
                        worst["I3"] = (inter, tag)
                    if tot > worst["fresh_total"][0]:
                        worst["fresh_total"] = (tot, tag)
                    if inter > 3:
                        breaks.append(("I3", tag, gap, lp, lm))
                    if inter > 2 and len([b for b in breaks if b[0] == "I2"]) < 5:
                        breaks.append(("I2", tag, gap, lp, lm))
        del E
    print("Nmax=%d, %d random CM law pairs, seed %d" % (Nmax, nlaws, seed))
    for k, (v, tag) in worst.items():
        print("  max %-12s = %d   at %s" % (k, v, tag))
    print("cases breaking a statement (first few of each):")
    seen = {}
    for name, tag, gap, lp, lm in breaks:
        seen[name] = seen.get(name, 0) + 1
        if seen[name] > 3:
            continue
        line = "  %s: %s  (min rel gap %.1e)" % (name, tag, gap)
        if getattr(lp, "exact", None) and getattr(lm, "exact", None) and tag[2] <= 260:
            st = {"fair": 0, "plus": 1, "minus": -1}[tag[3]]
            Pex = exact_law(lp.exact, lm.exact, tag[2], st)
            mx = exact_modes(Pex)
            line += "  exact: modes at %s" % [a for a, b in mx]
        print(line)
    print("total break counts:", seen)
