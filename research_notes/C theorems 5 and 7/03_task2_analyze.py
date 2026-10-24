"""Onset tables from the 03_task2_<config>.json files.
For g0 in (0.5, 1.0): cells with leading gap >= g0 and an admissible tau (T q_max < 0.97 N).
Onset = smallest listed N such that no cell of that kind is wrong at that N or at any larger listed N."""
import os, sys, json, glob
HERE = os.path.dirname(os.path.abspath(__file__))
names = sys.argv[1:] or [os.path.basename(p)[9:-5] for p in sorted(glob.glob(os.path.join(HERE, "03_task2_*.json")))]
for g0 in (0.5, 0.75):
    print(f"\n## leading gap >= {g0}")
    print("| config | R | b | b/R | U | M | min mu | N list | #cells ok/total (per N) | N_adm (all 9 tau admissible) | tau slices evaluated at the largest N | onset N | wrong cells at the largest N (tau, pair, delta, pred->exact, leading gap) |")
    print("|---|---:|---:|---:|---:|---:|---:|---|---|---:|---:|---:|---|")
    for name in names:
        p = os.path.join(HERE, f"03_task2_{name}.json")
        if not os.path.exists(p):
            continue
        d = json.load(open(p))
        Ns = sorted({r["N"] for r in d["results"]})
        per = {}
        adm = {}
        for N in Ns:
            rs = [r for r in d["results"] if r["N"] == N]
            adm[N] = all(r["admissible"] for r in rs)
            skipped = sum(1 for r in rs if r.get("skipped"))
            wrong, tot, wl = 0, 0, []
            for r in rs:
                if not r["admissible"]:
                    continue
                for c in r["cells"]:
                    if c["gap"] >= g0:
                        tot += 1
                        if c["pred"] != c["exact"]:
                            wrong += 1
                            wl.append((round(r["tau"], 3), (c["i"] + 1, c["j"] + 1), round(c["delta"], 2),
                                       tuple(x + 1 for x in c["pred"]), tuple(x + 1 for x in c["exact"]), round(c["gap"], 2)))
            per[N] = (wrong, tot, wl)
        # onset: scanning from the largest N downward
        onset = None
        for N in reversed(Ns):
            if per[N][0] == 0:
                onset = N
            else:
                break
        Nadm = next((N for N in Ns if adm[N]), None)
        last = per[Ns[-1]]
        rl = [r for r in d["results"] if r["N"] == Ns[-1]]
        ncov = f"{sum(1 for r in rl if r['admissible'] and not r.get('skipped'))}/9"
        worst = "; ".join(f"{a}" for a in last[2][:3]) + (" ..." if len(last[2]) > 3 else "")
        s = ", ".join(f"{N}:{per[N][1]-per[N][0]}/{per[N][1]}" for N in Ns)
        print(f"| {name} | {d['R']:.3f} | {d['b']:.3f} | {d['b']/d['R']:.3f} | {d['U']:.1f} | {d['M']:.0f} | {min(d['mu']):.3f} | {Ns[0]}..{Ns[-1]} | {s} | {Nadm} | {ncov} | {('<= '+str(onset)) if onset == Ns[0] else (onset if onset else 'beyond '+str(Ns[-1]))} | {worst} |")
