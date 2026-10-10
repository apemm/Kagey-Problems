"""Two checks for the sleep example (Section `sec:sleep`).

1. The profile of the likelihood of the budgets in the triangle flow j, on the
   real data: the fit with j = 0 against the best fit, and where the best fit sits.
2. The same fit on data simulated from the chain fitted to the full sequences
   (its own stationary start, 659 windows of 60 epochs), REPS times: what the
   budgets give for the two-way flows and for |j| when the model holds.

Run:  python -B sleep_checks.py      (about ten minutes)
Writes data_sleep_edf/checks.json .
"""
import json

import numpy as np
from scipy.optimize import minimize

import sleep_application as sa
import sleep_data as sd

REPS = 24


def fit_no_flow(K, starts):
    """Maximum likelihood from the budgets with j = 0 (a reversible chain)."""
    cells, mult = np.unique(K[:, :2], axis=0, return_counts=True)

    def nll(th):
        e = np.exp(np.append(th[:2], 0.0))
        pi = e / e.sum()
        c = np.exp(th[2:5])
        P = sa.chain(pi, c, 0.0)
        if (P < 0).any():
            return 1e12
        p = sa.count_law(P, pi)[cells[:, 0], cells[:, 1]]
        return 1e12 if (p <= 0).any() else -float(mult @ np.log(p))

    best = None
    for th0 in starts:
        r = minimize(nll, th0[:5], method="Nelder-Mead", options={"xatol": 1e-7, "fatol": 1e-9, "maxiter": 6000})
        r = minimize(nll, r.x, method="Nelder-Mead", options={"xatol": 1e-7, "fatol": 1e-9, "maxiter": 6000})
        if best is None or r.fun < best.fun:
            best = r
    return best.fun


def main():
    ws = [w for _, w in sd.windows(sa.NW)]
    K = np.array([np.bincount(w, minlength=3) for w in ws])
    full = sa.fit_budgets(K, sa.starts_for(K))
    nll0 = fit_no_flow(K, sa.starts_for(K))
    out = {"nll_best": full["nll"], "nll_no_flow": nll0, "lr": 2 * (nll0 - full["nll"]),
           "absj": float(full["j"]), "c": full["c"].tolist(),
           "on_boundary": bool(abs(full["j"] - full["c"][1]) < 1e-6 * full["c"][1])}
    print("real data: -log likelihood %.3f at the best fit, %.3f with j = 0, likelihood ratio statistic %.2f"
          % (full["nll"], nll0, out["lr"]))
    print("           |j| = %.4f per 1000 epochs, two-way flow awake-REM = %.4f, on the boundary: %s"
          % (1000 * full["j"], 1000 * full["c"][1], out["on_boundary"]))

    P = sa.fit_paths(ws)["P"]
    w_, v_ = np.linalg.eig(P.T)
    st = np.real(v_[:, np.argmax(np.real(w_))])
    st /= st.sum()
    f = st[:, None] * P
    ctrue = np.array([f[a, b] + f[b, a] for a, b in sa.PAIRS])
    jtrue = float(f[0, 1] - f[1, 0])
    print("chain fitted to the full sequences, with its own stationary law %s:" % np.round(st, 3))
    print("   two-way flows %s, triangle flow %.2f (per 1000 epochs)" % (np.round(1000 * ctrue, 2), 1000 * jtrue))
    rng = np.random.default_rng(2026)
    cum = np.cumsum(P, axis=1)
    rows = []
    for rep in range(REPS):
        sim = []
        for _ in range(len(ws)):
            x = np.empty(sa.NW, dtype=int)
            x[0] = rng.choice(3, p=st)
            u = rng.random(sa.NW - 1)
            for t in range(sa.NW - 1):
                x[t + 1] = int((u[t] > cum[x[t]]).sum())
            sim.append(x)
        Ks = np.array([np.bincount(w, minlength=3) for w in sim])
        b = sa.fit_budgets(Ks, sa.starts_for(Ks))
        rows.append([*(1000 * b["c"]), 1000 * b["j"]])
        print("   replicate %2d: c = %s, |j| = %.3f" % (rep + 1, np.round(rows[-1][:3], 2), rows[-1][3]), flush=True)
    R = np.array(rows)
    at_zero = float((R[:, 3] < 0.05).mean())
    at_wall = float((np.abs(R[:, 3] - R[:, 1]) < 1e-3 * R[:, 1]).mean())
    out.update({"true_c": (1000 * ctrue).tolist(), "true_j": 1000 * jtrue, "reps": REPS,
                "c_mean": R[:, :3].mean(0).tolist(), "c_sd": R[:, :3].std(0, ddof=1).tolist(),
                "j_mean": float(R[:, 3].mean()), "j_sd": float(R[:, 3].std(ddof=1)),
                "j_at_zero": at_zero, "j_at_boundary": at_wall})
    print("synthetic: c mean %s, sd %s" % (np.round(out["c_mean"], 2), np.round(out["c_sd"], 2)))
    print("           |j| mean %.2f, sd %.2f, share near 0: %.2f, share on the boundary: %.2f"
          % (out["j_mean"], out["j_sd"], at_zero, at_wall))
    (sd.DATA / "checks.json").write_text(json.dumps(out, indent=1), encoding="utf-8")
    print("wrote checks.json")


if __name__ == "__main__":
    main()
