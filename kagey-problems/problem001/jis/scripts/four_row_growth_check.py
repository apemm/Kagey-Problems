"""Cross-checks of the four-row growth constant rho.

Reads jis/data/four_row_recurrence.json and four_row_counts.json and checks:
1. every root of every factor of Q_4 has modulus at least 1/rho, with equality
   only at the real root 1/rho itself (so the dominant singularity is unique);
2. the per-partition denominators: their dominant factor, root and pole order;
3. power iteration on the singleton transition matrix S_F of each machine gives
   the spectral radius, which must match the partition's growth constant;
4. a_4(m) / (m^4 rho^m) at large m approaches the leading constant c.

Writes jis/data/four_row_growth_check.json.
"""
import json
import os
import sys
import time

import sympy
from sympy import Poly, symbols

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from four_row_machines import load_all  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "data")


def power_iteration(machine, iters=3000):
    """Spectral radius of the singleton transition matrix (letters 1,2,4,8)."""
    trans = machine["transitions"]
    n = machine["state_count"]
    v = [1.0] * n
    lam = 0.0
    for _ in range(iters):
        w = [0.0] * n
        for s in range(n):
            vs = v[s]
            if vs == 0.0:
                continue
            row = trans[s]
            for k in range(4):
                t = row[k]
                if t >= 0:
                    w[t] += vs
        norm = max(w)
        lam = norm
        v = [x / norm for x in w]
    return lam


def main():
    t0 = time.time()
    z = symbols("z")
    with open(os.path.join(DATA, "four_row_recurrence.json")) as f:
        rec = json.load(f)
    with open(os.path.join(DATA, "four_row_counts.json")) as f:
        cnt = json.load(f)
    rho = sympy.Float(rec["rho_60_digits"], 60)
    inv = 1 / rho
    # 1. all roots of all factors
    root_report = []
    unique = True
    for fac in rec["factors"]:
        fp = Poly(sympy.sympify(fac["factor"]), z)
        roots = fp.nroots(n=40, maxsteps=200)
        mods = sorted(abs(complex(r)) for r in roots)
        closest = min(mods)
        root_report.append({"factor_degree": fac["degree"], "multiplicity": fac["multiplicity"],
                            "min_root_modulus": closest})
        for r in roots:
            rr = complex(r)
            if abs(rr) < float(inv) * (1 - 1e-12):
                unique = False
            if abs(abs(rr) - float(inv)) < 1e-12 and abs(rr.imag) > 1e-12:
                unique = False
    # 2. per-partition dominant factor
    per = {}
    for name, info in rec["per_partition"].items():
        Qf = sympy.sympify(info["denominator_factored"])
        best = None
        for f, mult in sympy.factor_list(Qf, z)[1]:
            fp = Poly(f, z)
            for r in fp.nroots(n=40, maxsteps=200):
                rr = complex(r)
                if abs(rr.imag) < 1e-25 and rr.real > 0:
                    if best is None or rr.real < best[0]:
                        best = (rr.real, str(f), mult)
        per[name] = {"order": info["order"], "rho_F": 1 / best[0],
                     "dominant_factor": best[1], "pole_order": int(best[2])}
    # 3. power iteration
    for name, m in load_all():
        per[name]["spectral_radius_of_S_F_power_iteration"] = power_iteration(m)
        per[name]["agreement_digits"] = -sympy.log(
            abs(per[name]["rho_F"] - per[name]["spectral_radius_of_S_F_power_iteration"]) /
            per[name]["rho_F"], 10).evalf(4) if abs(
            per[name]["rho_F"] - per[name]["spectral_radius_of_S_F_power_iteration"]) > 0 else "exact"
        per[name]["agreement_digits"] = str(per[name]["agreement_digits"])
    # 4. leading constant from the terms
    c = sympy.Float(rec["leading_constant_c"], 30)
    checks = {}
    for m in (500, 1000, 1500):
        a = sympy.Integer(cnt["a4"][str(m)])
        val = a / (sympy.Integer(m) ** 4 * rho ** m)
        checks[str(m)] = {"a4_over_m4_rho_m": str(sympy.N(val, 15)),
                          "ratio_to_c": str(sympy.N(val / c, 12))}
    out = {
        "rho": str(sympy.Float(rho, 20)),
        "one_over_rho": str(sympy.Float(inv, 20)),
        "all_other_roots_have_larger_modulus": unique,
        "root_moduli_by_factor": root_report,
        "per_partition": per,
        "dominant_partition": max(per, key=lambda n: per[n]["rho_F"]),
        "leading_constant_c": str(c),
        "leading_constant_checks": checks,
        "upper_bound_base_212_to_quarter": float(212 ** 0.25),
        "seconds": round(time.time() - t0, 1),
    }
    with open(os.path.join(DATA, "four_row_growth_check.json"), "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
