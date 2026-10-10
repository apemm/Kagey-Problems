"""An application: what the time budgets of sleep say about its dynamics.

Data: the 44 hypnograms of the Sleep-EDF telemetry study (see sleep_data.py),
on three states (awake, non-REM, REM), cut into windows of 60 epochs (30 min).

For each window we keep only the time budget, namely the number of epochs in
each state. We fit a stationary three-state chain to the budgets alone, by
maximum likelihood with the exact law of the count vector (dynamic program),
in the coordinates (pi, c, j) of the note: stationary law, two-way flows, and
the flow j around the triangle awake -> non-REM -> REM -> awake. The law of the
budgets is even in j, so only |j| can be found.

For comparison we fit the chain to the full sequences of the same windows
(transition counts), which is what the budgets throw away.

Run:  python -B sleep_application.py            point estimates, a minute
      python -B sleep_application.py --boot B   also B bootstrap resamples of the nights
Results go to data_sleep_edf/results.json .
"""
import json
import sys
from math import log

import numpy as np
from scipy.optimize import minimize

import sleep_data as sd

NW = 60
PAIRS = ((0, 1), (0, 2), (1, 2))
SIGN = {(0, 1): 1, (1, 2): 1, (2, 0): 1, (1, 0): -1, (2, 1): -1, (0, 2): -1}


def chain(pi, c, j):
    """Transition matrix with stationary law pi, two-way flows c and triangle flow j."""
    P = np.zeros((3, 3))
    for (a, b) in PAIRS:
        cab = c[PAIRS.index((a, b))]
        P[a, b] = 0.5 * (cab + SIGN[(a, b)] * j) / pi[a]
        P[b, a] = 0.5 * (cab + SIGN[(b, a)] * j) / pi[b]
    P[np.arange(3), np.arange(3)] = 1.0 - P.sum(1)
    return P


def count_law(P, mu, n=NW):
    """P(K = (k0, k1, n - k0 - k1)) for the chain started from mu, as an (n+1) x (n+1) array."""
    A = np.zeros((n + 1, n + 1, 3))
    A[1, 0, 0], A[0, 1, 1], A[0, 0, 2] = mu
    for _ in range(n - 1):
        flow = A @ P
        B = np.zeros_like(A)
        B[1:, :, 0] = flow[:-1, :, 0]
        B[:, 1:, 1] = flow[:, :-1, 1]
        B[:, :, 2] = flow[:, :, 2]
        A = B
    return A.sum(2)


def unpack(theta):
    """Unconstrained parameters to (pi, c, j) with j >= 0, or None if not a chain."""
    e = np.exp(np.append(theta[:2], 0.0))
    pi = e / e.sum()
    c = np.exp(theta[2:5])
    j = np.exp(theta[5])
    P = chain(pi, c, j)
    if (P < 0).any():
        return None
    return pi, c, j, P


def fit_budgets(K, starts):
    """Maximum likelihood from the count vectors K (rows) alone."""
    cells, mult = np.unique(K[:, :2], axis=0, return_counts=True)

    def nll(theta):
        u = unpack(theta)
        if u is None:
            return 1e12
        pi, c, j, P = u
        law = count_law(P, pi)
        p = law[cells[:, 0], cells[:, 1]]
        if (p <= 0).any():
            return 1e12
        return -float(mult @ np.log(p))

    best = None
    for th0 in starts:
        r = minimize(nll, th0, method="Nelder-Mead",
                     options={"xatol": 1e-6, "fatol": 1e-8, "maxiter": 6000, "maxfev": 6000})
        r = minimize(nll, r.x, method="Nelder-Mead",
                     options={"xatol": 1e-7, "fatol": 1e-9, "maxiter": 6000, "maxfev": 6000})
        if best is None or r.fun < best.fun:
            best = r
    pi, c, j, P = unpack(best.x)
    return {"pi": pi, "c": c, "j": j, "nll": best.fun, "theta": best.x}


def fit_paths(ws):
    """The chain fitted to the full sequences (transition counts within windows)."""
    N = np.zeros((3, 3))
    for w in ws:
        np.add.at(N, (w[:-1], w[1:]), 1)
    P = N / N.sum(1, keepdims=True)
    pi = N.sum(1) / N.sum()
    f = pi[:, None] * P
    c = np.array([f[a, b] + f[b, a] for a, b in PAIRS])
    J = np.array([f[0, 1] - f[1, 0], f[1, 2] - f[2, 1], f[2, 0] - f[0, 2]])
    return {"pi": pi, "c": c, "J": J, "j": float(J.mean()), "P": P}


def sigma(c, J):
    """Entropy production per epoch from two-way flows c (pairs 01, 02, 12) and net flows."""
    Jp = np.array([J[0], J[2], J[1]]) if np.ndim(J) else np.array([J, J, J])   # order of PAIRS
    Jp = np.abs(Jp)
    return float(sum(x * log((cc + x) / (cc - x)) for cc, x in zip(c, Jp) if x > 0))


def starts_for(K):
    comp = K.mean(0) / NW
    base = np.array([log(comp[0] / comp[2]), log(comp[1] / comp[2])])
    out = []
    for cs in (0.02, 0.05):
        for j0 in (1e-4, 1e-3, 5e-3):
            out.append(np.concatenate([base, np.log([cs, cs / 5, cs / 2]), [log(j0)]]))
    return out


def summary(ws):
    K = np.array([np.bincount(w, minlength=3) for w in ws])
    b = fit_budgets(K, starts_for(K))
    p = fit_paths(ws)
    return {
        "budgets": {"pi": b["pi"].tolist(), "c": b["c"].tolist(), "absj": float(b["j"]),
                    "sigma": sigma(b["c"], b["j"]), "nll": b["nll"]},
        "paths": {"pi": p["pi"].tolist(), "c": p["c"].tolist(), "J": p["J"].tolist(),
                  "sigma": sigma(p["c"], p["J"]), "P": p["P"].tolist()},
    }


def main():
    win = sd.windows(NW)
    names = sorted({n for n, _ in win})
    by_night = {n: [w for m, w in win if m == n] for n in names}
    ws = [w for _, w in win]
    res = {"windows": len(ws), "nights": len(names), "epochs_per_window": NW, "point": summary(ws)}
    pt = res["point"]
    print("windows %d from %d nights" % (len(ws), len(names)))
    for k in ("budgets", "paths"):
        print(" %-8s pi %s  c*1000 %s" % (k, np.round(pt[k]["pi"], 3), np.round(1000 * np.array(pt[k]["c"]), 2)))
    print(" budgets  |j|*1000 = %.3f   sigma*1000 = %.3f" % (1000 * pt["budgets"]["absj"], 1000 * pt["budgets"]["sigma"]))
    print(" paths    J*1000  = %s   sigma*1000 = %.3f" % (np.round(1000 * np.array(pt["paths"]["J"]), 3), 1000 * pt["paths"]["sigma"]))
    if "--boot" in sys.argv:
        B = int(sys.argv[sys.argv.index("--boot") + 1])
        rng = np.random.default_rng(131)
        boots = []
        for b in range(B):
            pick = rng.choice(names, size=len(names), replace=True)
            wsb = [w for n in pick for w in by_night[n]]
            boots.append(summary(wsb))
            if (b + 1) % 10 == 0:
                print("  bootstrap %d of %d" % (b + 1, B), flush=True)
        res["boot"] = boots
    out = sd.DATA / "results.json"
    out.write_text(json.dumps(res, indent=1), encoding="utf-8")
    print("wrote", out.name)


if __name__ == "__main__":
    main()
