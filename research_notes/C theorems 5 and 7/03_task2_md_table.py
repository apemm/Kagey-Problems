"""Compact onset table (six-face comparison) for 03_T5_numerics.md."""
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from importlib import import_module
sc = import_module("03_task2_scan")
order = ["base", "path", "start_a", "start_b", "start_c", "unequal_a", "unequal_b", "unequal_start", "weak13_a", "weak13_b"]
print("| config | pi | min mu | b/R | R | U | N_adm | tau slices evaluated at largest N | onset, gap>=0.75 | onset, gap>=0.5 |")
print("|---|---|---:|---:|---:|---:|---:|---:|---:|---:|")
for name in order:
    d = json.load(open(os.path.join(HERE, f"03_task2_{name}.json")))
    Ns = sorted({r["N"] for r in d["results"]})
    adm = next((N for N in Ns if all(r["admissible"] for r in d["results"] if r["N"] == N)), None)
    rl = [r for r in d["results"] if r["N"] == Ns[-1]]
    cov = sum(1 for r in rl if r["admissible"] and not r.get("skipped"))
    ons = []
    for g0 in (0.75, 0.5):
        wrongN = {}
        for N in Ns:
            w = 0
            for r in d["results"]:
                if r["N"] == N and r["admissible"] and not r.get("skipped"):
                    w += sum(1 for c in r["cells"] if c["gap"] >= g0 and c["pred"] != c["exact"])
            wrongN[N] = w
        on = None
        for N in reversed(Ns):
            if wrongN[N] == 0:
                on = N
            else:
                break
        ons.append(("<= %d" % on if on == Ns[0] else str(on)) if on else "> %d" % Ns[-1])
    pi = sc.CONFIGS[name][0]
    print(f"| {name} | {tuple(pi)} | {min(d['mu']):.3f} | {d['b']/d['R']:.3f} | {d['R']:.2f} | {d['U']:.0f} | {adm} | {cov}/9 | {ons[0]} | {ons[1]} |")
