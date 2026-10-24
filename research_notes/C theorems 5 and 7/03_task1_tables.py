"""Tables and fits for Task 1 from 03_task1_results.json."""
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
from importlib import import_module
T1 = import_module("03_task1_compute")
core = import_module("03_core")
MU, q, H, tau0 = T1.MU, T1.q, T1.H, T1.tau0
res = json.load(open(os.path.join(HERE, "03_task1_results.json")))

pairs = {}
for r in res["pair"]:
    if r.get("tauN") is None:
        continue
    pairs.setdefault((r["i"], r["j"]), {})[r["N"]] = r
print("Generator: pi=(.25,.35,.40), conductances c12=.45 c13=.34 c23=.37 (labels 1,2,3 below), mu=(.3,.3,.4)")
print("R = %.5f  b = %.5f  H = %.4f  tau_0 = %.5f  U = %.3f  M = %.1f" % (T1.R, T1.b, H, tau0, T1.U, T1.M))
print("exit rates q =", np.round(q, 5), "  d_i = q_i - q_1 =", np.round(q - q[0], 5))
fitrows = []
for (i, j) in sorted(pairs):
    t = core.limit_t_ij(T1.Q, i, j, H)
    odd = ", ".join(f"N={N}:{pairs[(i,j)][N]['n_up']}up/{pairs[(i,j)][N]['n_down']}down" for N in sorted(pairs[(i,j)]) if pairs[(i,j)][N]['n_up'] != 1 or pairs[(i,j)][N]['n_down'] != 0)
    print(f"\n### ordered pair (i,j) = ({i+1},{j+1}); limiting t_ij = {t:.6f}; sign changes of (log pair - log best singleton) on an 18-point tau grid: " + (odd if odd else "exactly one up-crossing and no down-crossing at every N"))
    print("| N | tau_N (exact) | t_ij | prediction t(1-loglogN/(2logN)) | (tau_N - pred) log N | (t - tau_N)/t | T_N | kappa_N = log N - T_N/t - (1/2)log T_N |")
    print("|---:|---:|---:|---:|---:|---:|---:|---:|")
    Ns = sorted(pairs[(i, j)])
    arr = []
    for N in Ns:
        tn = pairs[(i, j)][N]["tauN"]
        L = np.log(N)
        pred = t * (1 - np.log(L) / (2 * L))
        TN = tn * L
        kap = L - TN / t - 0.5 * np.log(TN)
        print(f"| {N} | {tn:.6f} | {t:.6f} | {pred:.6f} | {(tn-pred)*L:.4f} | {(t-tn)/t:.6f} | {TN:.3f} | {kap:.4f} |")
        arr.append((N, tn, L, TN, kap))
    arr = np.array(arr)
    for N0 in (1000, 5000):
        sel = arr[:, 0] >= N0
        if sel.sum() < 4:
            continue
        N_, tn_, L_, TN_, kap_ = arr[sel].T
        eps = (t - tn_) / t
        X = np.column_stack([np.log(L_) / L_, 1 / L_])
        co, *_ = np.linalg.lstsq(X, eps, rcond=None)
        # free-exponent fit  y = logN - T/t = p log T + kappa
        y = L_ - TN_ / t
        X2 = np.column_stack([np.log(TN_), np.ones_like(TN_)])
        co2, *_ = np.linalg.lstsq(X2, y, rcond=None)
        X3 = np.column_stack([np.log(TN_), np.ones_like(TN_), 1 / TN_])
        co3, *_ = np.linalg.lstsq(X3, y, rcond=None)
        # one-parameter: fix p=1/2, compare spread of kappa_N
        print(f"fit N>={N0} ({sel.sum()} points): (t-tau_N)/t = a loglogN/logN + c/logN : a = {co[0]:.4f}, c = {co[1]:.4f};"
              f"  free-exponent y=logN-T_N/t = p log T_N + kappa: p = {co2[0]:.4f}, kappa = {co2[1]:.4f};"
              f"  with 1/T term: p = {co3[0]:.4f}, kappa = {co3[1]:.4f}, beta = {co3[2]:.3f};"
              f"  kappa_N range with p=1/2: [{kap_.min():.4f}, {kap_.max():.4f}]")
        fitrows.append(((i + 1, j + 1), N0, co[0], co2[0], co3[0]))
print("\nSummary of fitted coefficients (pair, N0, a_loglog, p_free, p_with_1/T)")
for r in fitrows:
    print(r[0], r[1], f"{r[2]:.3f} {r[3]:.3f} {r[4]:.3f}")

print("\n### Singleton switch x_{i,N} at tau_0 (retained pair (i,1)); exact closed form for the singleton crossing")
print("| i | N | x_{i,N} | x_i = q_i - q_1 | (x_{i,N} - x_i) log N | log(mu_1/mu_i)/tau_0 | winner transitions in window (N<=6000) | max of (log pair - log best singleton) over the window / at x_N |")
print("|---:|---:|---:|---:|---:|---:|---|---:|")
for r in sorted(res["switch"], key=lambda r: (r["i"], r["N"])):
    L = np.log(r["N"])
    tr = r.get("transitions")
    trs = "; ".join(f"{a:.4f}: {tuple(x+1 for x in b)}->{tuple(x+1 for x in c)}" for a, b, c in tr) if tr is not None else "n/a (N>6000): top3 at x_N=" + str(r.get("at_dN_top"))
    pm = r["max_pair_margin_over_window"] if "max_pair_margin_over_window" in r else -r["pair_margin_at_dN"]
    print(f"| {r['i']+1} | {r['N']} | {r['xN']:.6f} | {r['x']:.6f} | {(r['xN']-r['x'])*L:.4f} | {np.log(MU[0]/MU[r['i']])/tau0:.4f} | {trs} | {pm:.3f} |")

print("\n### Local exponent p_eff = 1/2 + d kappa_N / d log T_N between N=10^4 and the largest N available (p=1/2 is the prediction)")
for (i, j) in sorted(pairs):
    t = core.limit_t_ij(T1.Q, i, j, H)
    Ns = sorted(n for n in pairs[(i, j)] if n >= 10000)
    def kT(N):
        tn = pairs[(i, j)][N]["tauN"]; L = np.log(N); TN = tn * L
        return L - TN / t - 0.5 * np.log(TN), np.log(TN)
    k0, l0 = kT(Ns[0]); k1, l1 = kT(Ns[-1])
    print(f"pair ({i+1},{j+1}): N {Ns[0]} -> {Ns[-1]}: kappa {k0:.4f} -> {k1:.4f}, log T {l0:.3f} -> {l1:.3f}, p_eff = {0.5 + (k1-k0)/(l1-l0):.3f}; "
          f"predicted limiting residual (tau_N - pred) log N -> -t(1/2 log t + kappa) = {-t*(0.5*np.log(t)+k1):.2f}")
