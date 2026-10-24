"""Tables of the n_k = 1 margins from 03_task2_n1_<config>[_big].json."""
import os, sys, json, glob
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from importlib import import_module
sc = import_module("03_task2_scan"); core = import_module("03_core")
for name in sys.argv[1:]:
    res = []
    for p in sorted(glob.glob(os.path.join(HERE, f"03_task2_n1_{name}*.json"))):
        res += json.load(open(p))
    Ns = sorted({r["N"] for r in res})
    Q, pi, mu, S, R, b, q = sc.build(name)
    H, tau0, U, M = core.design_constants(R, b)
    taus, _ = sc.grids(R, U)
    print(f"\n### {name}: R={R:.3f} b={b:.4f} U={U:.1f} M={M:.0f}")
    print("| tau | " + " | ".join(f"N={N:.0e}" for N in Ns) + " |")
    print("|---:|" + "---:|" * len(Ns))
    for ti in range(9):
        row = []
        seen = False
        for N in Ns:
            r = next((x for x in res if x["N"] == N and x["ti"] == ti), None)
            if r is None:
                row.append(""); continue
            seen = True
            if r["status"] == "inadmissible": row.append("-")
            elif r["status"] == "skipped": row.append("s")
            elif r["min_margin"] is None: row.append("no cells")
            else: row.append(f"{r['min_margin']:.2f}" + (f" ({r['nneg']} neg)" if r["nneg"] else ""))
        if seen:
            print(f"| {taus[ti]:.3f} | " + " | ".join(row) + " |")
