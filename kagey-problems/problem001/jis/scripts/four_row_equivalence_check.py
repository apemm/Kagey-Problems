"""Check that the exported four-row machines accept the words of Lemma "six columns of memory".

For each pair set F this script builds the automaton of Lemma "six columns of memory"
straight from the definition. A state is the last six columns read and the set of pairs
of F already used. A new column is accepted when the last seven columns pass the three
conditions of the lemma. No tilted rectangle ending in the new column is hidden. No such
tilted rectangle shares its presentation with an axis-aligned rectangle on its own
columns and the double columns. No other tilted rectangle in the seven columns shares
its presentation. Each pair of F occurs in exactly one double column, so the double
columns are stood in for by four extra columns to the right of the window. The
rectangles are listed from the definition, as four points that split into two diagonals
with the same midpoint and the same length. Points are one-based (column, row).

A word is accepted when every pair of F has been used once. The script then runs a
breadth-first search on the product of this automaton with the exported machine in
jis/data/four_row_machines, read by four_row_machines.py, with the register of used
pairs shared. Every listed machine state is accepting, so on both sides a word is
accepted exactly when it is read to the end with all four pairs used. The two accept the
same words if no reachable pair of states has one side
alive and the other side dead while the live side can still reach an accepting state.
The script counts these mismatches and also the raw one-sided cases.

Writes jis/data/four_row_equivalence_check.json.
"""
import json
import sys
import time
from collections import defaultdict, deque
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import four_row_machines as fm  # noqa: E402

DATA = HERE.parent / "data"
H = 4
WIN = 7
PARTS = {"{1,2}|{3,4}": ((1, 2), (3, 4)),
         "{1,3}|{2,4}": ((1, 3), (2, 4)),
         "{1,4}|{2,3}": ((1, 4), (2, 3))}
FILES = {"{1,2}|{3,4}": "machine_56910.json",
         "{1,3}|{2,4}": "machine_36912.json",
         "{1,4}|{2,3}": "machine_351012.json"}


def rectangles(h, m):
    """All rectangles of the h x m grid as frozensets of (column, row) points."""
    pts = [(c, r) for c in range(1, m + 1) for r in range(1, h + 1)]
    groups = defaultdict(list)
    for p, q in combinations(pts, 2):
        key = (p[0] + q[0], p[1] + q[1], (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)
        groups[key].append((p, q))
    out = set()
    for lst in groups.values():
        for (p, q), (r, s) in combinations(lst, 2):
            st = frozenset((p, q, r, s))
            if len(st) == 4:
                out.add(st)
    return sorted(out, key=lambda s: sorted(s))


def is_axis(R):
    return len({p[0] for p in R}) == 2


# rectangles of a 4 x 11 local grid: columns 1..7 are the window, 8..11 stand in for the doubles
LOC = rectangles(H, WIN + 4)
TILT_WIN = [R for R in LOC if not is_axis(R) and max(p[0] for p in R) <= WIN]
TILT_LAST = [R for R in TILT_WIN if max(p[0] for p in R) == WIN]
AXIS_LOC = [R for R in LOC if is_axis(R)]


def mask(letter):
    return sum(1 << (r - 1) for r in letter)


def check(pname):
    machine = fm.load_machine(FILES[pname])
    alpha = machine["alphabet"]
    trans = machine["transitions"]
    a, b = PARTS[pname]
    F = [frozenset((x, y)) for x in a for y in b]
    letters = [frozenset((r,)) for r in range(1, 5)] + F
    assert sorted(alpha) == sorted(mask(L) for L in letters)
    col = {L: k for k, L in enumerate(alpha)}
    virt = {(WIN + 1 + k, r) for k, e in enumerate(F) for r in e}
    cache = {}

    def ok(window):
        """The new column, the last letter of window, passes the three conditions."""
        if window in cache:
            return cache[window]
        off = WIN - len(window)
        S = set(virt)
        for k, L in enumerate(window):
            for r in L:
                S.add((off + 1 + k, r))
        lo = off + 1

        def pres(R):
            return frozenset(p for p in R if p not in S)

        inwin = [R for R in TILT_WIN if min(p[0] for p in R) >= lo]
        res = True
        for T in TILT_LAST:
            if min(p[0] for p in T) < lo:
                continue
            P = pres(T)
            if not P:
                res = False
                break
            if len(P) > 2:
                continue
            if any(min(p[0] for p in R) >= lo and pres(R) == P for R in AXIS_LOC):
                res = False
                break
            if any(T2 != T and pres(T2) == P for T2 in inwin):
                res = False
                break
        cache[window] = res
        return res

    # the automaton of the lemma: states (last six columns, used pairs)
    start = ((), 0)
    edges = {}
    seen_mine = {start}
    q = deque([start])
    while q:
        s = q.popleft()
        last, used = s
        out = []
        for li, L in enumerate(letters):
            nu = used
            if li >= 4:
                bit = 1 << (li - 4)
                if used & bit:
                    out.append(None)
                    continue
                nu |= bit
            w = last + (L,)
            if not ok(w[-WIN:]):
                out.append(None)
                continue
            t = (w[-(WIN - 1):], nu)
            out.append(t)
            if t not in seen_mine:
                seen_mine.add(t)
                q.append(t)
        edges[s] = out

    # states of the lemma's automaton that can still reach an accepting state
    rev = defaultdict(list)
    for s, out in edges.items():
        for t in out:
            if t is not None:
                rev[t].append(s)
    co_mine = {s for s in seen_mine if s[1] == 15}
    dq = deque(co_mine)
    while dq:
        t = dq.popleft()
        for s in rev[t]:
            if s not in co_mine:
                co_mine.add(s)
                dq.append(s)

    # the same for the exported machine with the register of used pairs
    def step_theirs(g, used, li):
        if li >= 4:
            if used >> (li - 4) & 1:
                return None
            used |= 1 << (li - 4)
        g2 = trans[g][col[mask(letters[li])]]
        return None if g2 == -1 else (g2, used)

    reach_theirs = {(0, 0)}
    dq = deque([(0, 0)])
    rev_t = defaultdict(list)
    while dq:
        s = dq.popleft()
        for li in range(len(letters)):
            t = step_theirs(s[0], s[1], li)
            if t is None:
                continue
            rev_t[t].append(s)
            if t not in reach_theirs:
                reach_theirs.add(t)
                dq.append(t)
    co_theirs = {s for s in reach_theirs if s[1] == 15}
    dq = deque(co_theirs)
    while dq:
        t = dq.popleft()
        for s in rev_t[t]:
            if s not in co_theirs:
                co_theirs.add(s)
                dq.append(s)

    # product search with the register shared
    ps = (start, 0)
    seen = {ps}
    dq = deque([ps])
    mine_only = theirs_only = mine_only_live = theirs_only_live = 0
    examples = []
    while dq:
        s, g = dq.popleft()
        for li in range(len(letters)):
            if li >= 4 and s[1] >> (li - 4) & 1:
                continue  # both reject a pair used twice
            t = edges[s][li]
            nxt = step_theirs(g, s[1], li)
            if t is not None and nxt is not None:
                assert nxt[1] == t[1]
                if (t, nxt[0]) not in seen:
                    seen.add((t, nxt[0]))
                    dq.append((t, nxt[0]))
            elif t is not None:
                mine_only += 1
                if t in co_mine:
                    mine_only_live += 1
                    if len(examples) < 10:
                        examples.append({"side": "lemma only", "last_columns": [sorted(L) for L in s[0]],
                                         "used": s[1], "letter": sorted(letters[li])})
            elif nxt is not None:
                theirs_only += 1
                if nxt in co_theirs:
                    theirs_only_live += 1
                    if len(examples) < 10:
                        examples.append({"side": "machine only", "last_columns": [sorted(L) for L in s[0]],
                                         "used": s[1], "letter": sorted(letters[li])})
    return {
        "machine_file": FILES[pname],
        "machine_states": machine["state_count"],
        "lemma_automaton_states": len(seen_mine),
        "lemma_automaton_coreachable_states": len(co_mine),
        "machine_with_register_reachable_states": len(reach_theirs),
        "product_pairs": len(seen),
        "one_sided_steps_lemma_only": mine_only,
        "one_sided_steps_machine_only": theirs_only,
        "mismatches_lemma_only": mine_only_live,
        "mismatches_machine_only": theirs_only_live,
        "examples": examples,
    }


def main():
    t0 = time.time()
    out = {"date": time.strftime("%Y-%m-%d"), "python": sys.version.split()[0],
           "coordinates": "one-based (column, row), (1,1) top-left",
           "window_columns": WIN, "pair_sets": {}}
    ok_all = True
    for p in PARTS:
        t = time.time()
        r = check(p)
        r["seconds"] = round(time.time() - t, 1)
        out["pair_sets"][p] = r
        good = r["mismatches_lemma_only"] == 0 and r["mismatches_machine_only"] == 0
        ok_all = ok_all and good
        print(p, "lemma states", r["lemma_automaton_states"], "product pairs", r["product_pairs"],
              "mismatches", r["mismatches_lemma_only"], r["mismatches_machine_only"],
              "%.0f s" % r["seconds"], flush=True)
    out["same_words_for_every_pair_set"] = ok_all
    out["seconds"] = round(time.time() - t0, 1)
    with open(DATA / "four_row_equivalence_check.json", "w") as f:
        json.dump(out, f, indent=1)
    print("same words for every pair set:", ok_all)


if __name__ == "__main__":
    main()
