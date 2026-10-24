"""Per-tau-slice onset: for each config and each of the 9 tau grid values, the number of wrong cells
(leading gap >= g0) at each listed N.  '-' = not admissible (T q_max >= 0.97 N), 's' = skipped for cost."""
import os, sys, json, glob
HERE = os.path.dirname(os.path.abspath(__file__))
g0 = float(sys.argv[1])
names = sys.argv[2:]
for name in names:
    p = os.path.join(HERE, f"03_task2_{name}.json")
    d = json.load(open(p))
    Ns = sorted({r["N"] for r in d["results"]})
    print(f"\n### {name}: R={d['R']:.3f} b={d['b']:.4f} b/R={d['b']/d['R']:.4f} U={d['U']:.1f} M={d['M']:.0f} mu={d['mu']} (gap >= {g0}); entries: wrong/total")
    print("| ti | tau | " + " | ".join(f"N={N}" for N in Ns) + " | onset(tau) |")
    print("|---:|---:|" + "---:|" * len(Ns) + "---:|")
    for ti in range(9):
        row, tau, last_bad, ok_seen = [], None, None, False
        for N in Ns:
            r = next(x for x in d["results"] if x["N"] == N and x["ti"] == ti)
            tau = r["tau"]
            if not r["admissible"]:
                row.append("-")
                continue
            if r.get("skipped"):
                row.append("s")
                continue
            cs = [c for c in r["cells"] if c["gap"] >= g0]
            w = sum(1 for c in cs if c["pred"] != c["exact"])
            row.append(f"{w}/{len(cs)}")
            if w:
                last_bad = N
        ev = [x for x in row if x not in ("-", "s")]
        if not ev:
            on = "n/a"
        elif last_bad is None:
            on = next(N for N, x in zip(Ns, row) if x not in ("-", "s")).__str__() + " (first admissible)"
        elif last_bad == Ns[-1] or all(x in ("-", "s") for x in row[Ns.index(last_bad) + 1:]):
            on = "> " + str(last_bad)
        else:
            on = "> " + str(last_bad)
        print(f"| {ti} | {tau:.3f} | " + " | ".join(row) + f" | {on} |")
