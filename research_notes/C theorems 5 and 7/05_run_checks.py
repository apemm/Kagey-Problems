"""Route T7-B driver: examples (27) and (34), random matrices, tied families, suppression.

Run:  py -I 05_run_checks.py   (writes 05_reconstruction_output.json and .txt next to it)
"""

import importlib.util
import json
import os
import random
import sys
from fractions import Fraction
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("core05", os.path.join(HERE, "05_core.py"))
core = importlib.util.module_from_spec(spec)
sys.modules["core05"] = core
spec.loader.exec_module(core)
import sympy as sp

LOG = []


def say(*a):
    s = " ".join(str(x) for x in a)
    print(s)
    LOG.append(s)


def name(f):
    return "{" + ",".join(str(i + 1) for i in f) + "}"


def rev_matrix(U, Hpairs, default):
    n = len(U)
    H = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            H[i][j] = H[j][i] = Hpairs.get((i + 1, j + 1), default)
    V = [[None if i == j else H[i][j] - U[i] for j in range(n)] for i in range(n)]
    assert all(V[i][j] >= 0 for i in range(n) for j in range(n) if i != j)
    return V, (U, H)


def rand_rev(n, rng, ur=3, hr=3):
    U = [rng.randint(0, ur) for _ in range(n)]
    H = [[None] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            H[i][j] = H[j][i] = max(U[i], U[j]) + rng.randint(0, hr)
    V = [[None if i == j else H[i][j] - U[i] for j in range(n)] for i in range(n)]
    return V, (U, H)


def rand_nonrev(n, rng, hi=4):
    return [[None if i == j else rng.randint(0, hi) for j in range(n)] for i in range(n)], None


def cyc_list(res):
    return [name(f) + "(D=%d)" % res["D"][f] for f in sorted(res["D"], key=lambda f: (len(f), f))
            if res["cycle"][f]]


def prefactors_at_depth(V, base, res, gamma):
    out = {}
    for f, d in res["D"].items():
        if d == gamma:
            D, a = core.prefactor(base, f)
            out[f] = a
    return out


def lower_envelope(gamma, res, base, n):
    """Limiting score m_F + x a_F for D(F) = gamma, m_F for D(F) > gamma (E: n-1)."""
    items = {}
    for f, d in res["D"].items():
        if d == gamma:
            items[f] = (len(f) - 1, core.prefactor(base, f)[1])
        elif d > gamma:
            items[f] = (len(f) - 1, sp.Integer(0))
    items[tuple(range(n))] = (n - 1, sp.Integer(0))
    xs = set()
    keys = list(items)
    for a, b in combinations(keys, 2):
        (ma, aa), (mb, ab) = items[a], items[b]
        if aa != ab:
            x = (mb - ma) / (aa - ab)
            if x > 0:
                xs.add(sp.nsimplify(x))
    xs = sorted(xs)
    pts = [sp.Integer(0)] + xs
    seq = []
    for k, lo in enumerate(pts):
        hi = pts[k + 1] if k + 1 < len(pts) else lo + 2
        x = (lo + hi) / 2
        sc = {f: items[f][0] + x * items[f][1] for f in keys}
        m = min(sc.values())
        w = [f for f in keys if sp.simplify(sc[f] - m) == 0]
        seq.append((lo, [name(f) for f in w]))
    return seq, items


# ---------------------------------------------------------------- 1. the two named examples
say("=" * 78)
say("SECTION 1. Named examples")
EX27 = rev_matrix([0, 1, 1, 1], {(1, 2): 2, (1, 3): 3, (2, 3): 3, (3, 4): 3, (1, 4): 5, (2, 4): 5}, None)
EX34 = rev_matrix([2, 0, 0], {(1, 2): 5, (1, 3): 5, (2, 3): 1}, None)
results = {}
for label, (V, rv) in (("ex27", EX27), ("ex34", EX34)):
    n = len(V)
    res, base = core.analyze(V, rv)
    say("-" * 78)
    say(label, "V =", V)
    say("cycles (truth, exit-probability definition):", ", ".join(cyc_list(res)))
    say("Theorem D consistency:", res["thmD"], "| singleton formula (8):", res["singleton_formula"],
        "| energy-cycle agrees:", res["energy_cycle_agrees"])
    for f in sorted(res["D"], key=lambda f: (len(f), f)):
        D, a = core.prefactor(base, f)
        assert D == res["D"][f]
        say("  F=%-8s D=%d  a_F=%-6s cycle=%-5s criterion=%s" % (name(f), D, a if a.is_Rational else sp.N(a, 10),
                                                                    res["cycle"][f], res["criterion"][f]))
    say("disagreements criterion vs truth:", res["disagreements"] or "none")
    results[label] = {"cycles": cyc_list(res), "disagreements": res["disagreements"]}
    # jump-chain cross-check
    bad = 0
    chk = 0
    for C in core.proper_faces(n):
        if len(C) == 1:
            continue
        for x in C:
            for y in C:
                if x != y:
                    chk += 1
                    if core.jump_chain_exit_exponent(V, C, x, y) != core.exit_exponent(V, base, C, x, y):
                        bad += 1
    say("jump-chain (sympy rational functions) vs scaled Cramer exponents: %d checked, %d mismatches" % (chk, bad))
    assert bad == 0
    if label == "ex27":
        a = {f: core.prefactor(base, f)[1] for f in [(0, 1), (0, 1, 2), (0, 1, 3)]}
        assert a[(0, 1)] == 2 and a[(0, 1, 2)] == sp.Rational(2, 3) and a[(0, 1, 3)] == 2
        say("a_12, a_123, a_124 =", a[(0, 1)], a[(0, 1, 2)], a[(0, 1, 3)], "(agree with (32))")
        seq, items = lower_envelope(3, res, base, n)
        say("limiting score envelope at gamma=3, winners per x-interval (left endpoint):")
        merged = []
        for lo, w in seq:
            if merged and merged[-1][1] == w:
                continue
            merged.append((lo, w))
        for lo, w in merged:
            say("   x >", lo, "->", w)
        results["ex27_window"] = [(str(lo), w) for lo, w in merged]
    if label == "ex34":
        assert res["D"][(1, 2)] == 5 and res["cycle"][(1, 2)] and res["D"][(0,)] == 3

# ---------------------------------------------------------------- 2. random matrices
say("=" * 78)
say("SECTION 2. Random integer cost matrices (seeded)")
rng = random.Random(20261024)
rand_table = []
dis_all = []
cases = []
for n, cnt in ((4, 20), (5, 15)):
    for _ in range(cnt):
        cases.append((n, "rev", rand_rev(n, rng)))
    for _ in range(cnt):
        cases.append((n, "nonrev", rand_nonrev(n, rng)))
tot_faces = 0
for idx, (n, kind, (V, rv)) in enumerate(cases):
    res, base = core.analyze(V, rv)
    tot_faces += len(res["D"])
    ncyc = sum(1 for f in res["cycle"] if res["cycle"][f] and len(f) > 1)
    ok = res["thmD"] and res["singleton_formula"] and res.get("energy_cycle_agrees", True)
    rand_table.append((idx, n, kind, ncyc, len(res["disagreements"]), ok))
    for d in res["disagreements"]:
        dis_all.append({"idx": idx, "n": n, "kind": kind, "V": V, **d})
    if not ok:
        say("  !! consistency failure at case", idx, V)
say("idx n kind    nonsingleton_cycles  disagreements  consistency(ThmD,eq8,energy)")
for r in rand_table:
    say("%3d %d %-7s %6d %14d %14s" % r)
say("total matrices:", len(cases), "| faces tested:", tot_faces, "| disagreements:", len(dis_all))
for d in dis_all:
    say("DISAGREEMENT", d)
results["random_disagreements"] = dis_all
results["random_count"] = len(cases)
results["random_faces"] = tot_faces

# ---------------------------------------------------------------- 3. tied families
say("=" * 78)
say("SECTION 3. Tied-depth families")
families = {}
families["F1 two equal pair-cycles (rev, 4 states)"] = rev_matrix([0, 0, 0, 0], {(1, 2): 1, (3, 4): 1}, 4)
families["F2 three equal cycles {12},{34},{5} (rev, 5 states)"] = rev_matrix(
    [0] * 5, {(1, 2): 1, (3, 4): 1, (1, 5): 2, (2, 5): 2, (3, 5): 2, (4, 5): 2}, 6)
families["F3 four equal singletons, complete symmetric (rev, 4 states)"] = rev_matrix([0] * 4, {}, 3)
families["F4 variant of (27): tied noncycle faces (rev, 4 states)"] = rev_matrix(
    [0, 1, 1, 1], {(1, 2): 2, (1, 3): 3, (2, 3): 3, (3, 4): 3, (1, 4): 6, (2, 4): 6}, None)
nr = [[None, 1, 5, 5], [2, None, 5, 5], [5, 5, None, 1], [5, 5, 2, None]]
families["F5 two identical non-reversible blocks (4 states)"] = (nr, None)
families["F7 equal-depth cycles nested in a deeper one (rev, 5 states)"] = rev_matrix(
    [0] * 5, {(1, 2): 1, (3, 4): 1, (1, 3): 3, (1, 4): 6, (2, 3): 6, (2, 4): 6,
              (1, 5): 5, (2, 5): 5, (3, 5): 5, (4, 5): 5}, None)

# F6: deterministic search for a non-reversible 5-state matrix with two disjoint
# nonsingleton cycles of equal depth
rng6 = random.Random(6)
found = None
for trial in range(5000):
    V, _ = rand_nonrev(5, rng6, 4)
    res, base = core.analyze(V, None)
    cs = [f for f in res["cycle"] if res["cycle"][f] and len(f) > 1]
    if any(set(a).isdisjoint(b) and res["D"][a] == res["D"][b] for a, b in combinations(cs, 2)):
        found = (V, None)
        say("F6 search: found at trial", trial)
        break
assert found
families["F6 non-reversible 5 states, two disjoint equal-depth nonsingleton cycles (searched)"] = found

fam_out = {}
for label, (V, rv) in families.items():
    n = len(V)
    res, base = core.analyze(V, rv)
    cs = [f for f in res["cycle"] if res["cycle"][f]]
    ties_disjoint = [(name(a), name(b), res["D"][a]) for a, b in combinations(cs, 2)
                     if set(a).isdisjoint(b) and res["D"][a] == res["D"][b]]
    ties_nested = [(name(a), name(b)) for a in cs for b in cs
                   if set(a) < set(b) and res["D"][a] == res["D"][b]]
    nc_tied = [(name(f)) for f in res["D"] if not res["cycle"][f]
               and any(res["cycle"][c] and set(c) < set(f) and res["D"][c] == res["D"][f] for c in res["D"])]
    say("-" * 78)
    say(label)
    say("  V =", V)
    say("  cycles:", ", ".join(cyc_list(res)))
    say("  disjoint equal-depth cycle pairs:", ties_disjoint or "none")
    say("  nested equal-depth cycle pairs:", ties_nested or "none")
    say("  noncycle faces whose D equals a contained cycle's D: %d" % len(nc_tied))
    say("  consistency (ThmD, eq8, energy):", res["thmD"], res["singleton_formula"], res.get("energy_cycle_agrees", "n/a"))
    say("  disagreements criterion vs truth:", res["disagreements"] or "none")
    fam_out[label] = {"V": V, "cycles": cyc_list(res), "disjoint_ties": ties_disjoint,
                      "nested_ties": ties_nested, "disagreements": res["disagreements"]}
results["families"] = fam_out

# nested equal-depth search (exhaustive 3-state in 0..3, random 4-state)
say("-" * 78)
say("Search for nested cycles C' < C with D(C') = D(C)")
cnt = 0
nested_found = []
thm_bad = 0
import itertools
for vals in itertools.product(range(4), repeat=6):
    V = [[None, vals[0], vals[1]], [vals[2], None, vals[3]], [vals[4], vals[5], None]]
    res, _ = core.analyze(V, None)
    cnt += 1
    thm_bad += int(not (res["thmD"] and res["singleton_formula"]))
    cs = [f for f in res["cycle"] if res["cycle"][f]]
    for a in cs:
        for b in cs:
            if set(a) < set(b) and res["D"][a] == res["D"][b]:
                nested_found.append(V)
    if res["disagreements"]:
        dis_all.append({"V": V, **res["disagreements"][0]})
say("3-state exhaustive costs in {0..3}:", cnt, "matrices; nested equal-depth cycles found:", len(nested_found))
rng4 = random.Random(44)
cnt4 = 0
for _ in range(1500):
    V, rv = (rand_rev(4, rng4) if rng4.random() < 0.5 else rand_nonrev(4, rng4))
    res, _ = core.analyze(V, rv)
    cnt4 += 1
    thm_bad += int(not (res["thmD"] and res["singleton_formula"]))
    cs = [f for f in res["cycle"] if res["cycle"][f]]
    for a in cs:
        for b in cs:
            if set(a) < set(b) and res["D"][a] == res["D"][b]:
                nested_found.append(V)
    if res["disagreements"]:
        dis_all.append({"V": V, **res["disagreements"][0]})
say("4-state random (half rev, half nonrev):", cnt4, "matrices; cumulative nested equal-depth found:", len(nested_found))
say("Theorem D / eq (8) consistency failures in the two searches:", thm_bad)
say("criterion disagreements over ALL searched matrices (incl. exhaustive/random searches):", len(dis_all))
results["nested_search"] = {"three_state_exhaustive": cnt, "four_state_random": cnt4,
                            "nested_equal_depth_found": len(nested_found)}
results["all_disagreements_total"] = len(dis_all)
results["search_thmD_failures"] = thm_bad

# ---------------------------------------------------------------- 4. suppression observable
say("=" * 78)
say("SECTION 4. Suppression observable: height at which the exact winner leaves F")
say("Field v_k = -M (k outside F), M = t^(-g).  g=2: strong, g=0: M=1, g=-3: weak (M = t^3).")
say("Winner = argmin over all nonempty G of (|G|-1) + t^(-h) lambda_G(v), lambda_G exact smallest")
say("eigenvalue (mpmath, 80+ digits, t = 1e-16 and 1e-24 must agree).  Sample heights j/4+1/8.")
say("class eq: first outside sample is D(F)+1/8 (leave at D(F)); lt: earlier; gt: later.")
designs = (2, 0, -1, -3)
supp_cases = [("ex27", EX27), ("ex34", EX34)] + [(k.split()[0], v) for k, v in families.items()]
rng_s = random.Random(77)
for k in range(6):
    supp_cases.append(("rand4-%d" % k, rand_rev(4, rng_s) if k % 2 == 0 else rand_nonrev(4, rng_s)))
for k in range(4):
    supp_cases.append(("rand5-%d" % k, rand_rev(5, rng_s) if k % 2 == 0 else rand_nonrev(5, rng_s)))
from collections import Counter
cnt = {g: Counter() for g in designs}
cnt_cyc = {(g, c): Counter() for g in designs for c in (True, False)}
kind_lt = Counter()
supp_rows = []
disagree_t = 0
for label, (V, rv) in supp_cases:
    n = len(V)
    res, base = core.analyze(V, rv)
    say("-" * 78)
    say(label)
    for F in core.proper_faces(n):
        row = {"case": label, "F": name(F), "D": res["D"][F], "cycle": res["cycle"][F]}
        txt = []
        for g in designs:
            outs = []
            for texp in (16, 24):
                w, hs = core.numeric_winners(V, F, g, texp)
                outs.append((w, hs))
            if outs[0][0] != outs[1][0]:
                disagree_t += 1
            w, hs = outs[0]
            out_set = w[-1]
            left = (not set(out_set) <= set(F))
            hleave = hs[-1] if left else None
            D = res["D"][F]
            if hleave is None:
                cls = "never"
            elif hleave == D + Fraction(1, 8):
                cls = "eq"
            elif hleave < D + Fraction(1, 8):
                cls = "lt"
            else:
                cls = "gt"
            cnt[g][cls] += 1
            cnt_cyc[(g, res['cycle'][F])][cls] += 1
            if cls == "lt":
                kind_lt["disjoint from F" if set(out_set).isdisjoint(F) else "overlaps F"] += 1
            row["g=%d" % g] = {"class": cls, "first_outside_h": None if hleave is None else str(hleave),
                               "winner": [i + 1 for i in out_set]}
            txt.append("g=%d:%s(%s)" % (g, cls, "-" if hleave is None else str(hleave - Fraction(1, 8))))
        supp_rows.append(row)
        say("  F=%-9s D=%d  %s" % (row["F"], row["D"], "  ".join(txt)))
say("COUNTS per design (rows = faces over all cases):")
for g in designs:
    say("  g=%d" % g, dict(cnt[g]))
for g in designs:
    for cflag in (True, False):
        say("  g=%d  F %s:" % (g, "cycle" if cflag else "noncycle"), dict(cnt_cyc[(g, cflag)]))
say("early-leaving (lt) winners:", dict(kind_lt))
say("(face, design) pairs where the t=1e-16 and t=1e-24 runs disagree:", disagree_t)
results["suppression_counts"] = {str(g): dict(cnt[g]) for g in designs}
results["suppression_counts_by_cycle"] = {"g=%d,cycle=%s" % k: dict(v) for k, v in cnt_cyc.items()}
results["suppression_lt_kind"] = dict(kind_lt)
results["suppression_rows"] = supp_rows
results["suppression_t_disagreements"] = disagree_t

with open(os.path.join(HERE, "05_reconstruction_output.json"), "w") as fh:
    json.dump(results, fh, indent=1, default=str)
with open(os.path.join(HERE, "05_reconstruction_output.txt"), "w") as fh:
    fh.write("\n".join(LOG) + "\n")
