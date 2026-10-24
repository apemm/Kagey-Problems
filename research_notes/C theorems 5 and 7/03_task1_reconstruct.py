"""Apply the C-I1 reconstruction to the exact finite-N coordinates (x_{i,N}, t_{ij,N}) of 03_task1_results.json.
Edges used: (1,2) with ordered pair (i,j)=(0,1) -> 't_01', (1,3) with (0,2), (2,3) with (1,2).
Three variants: raw t_{ij,N}; corrected t_{ij,N}/(1 - loglogN/(2logN)); and the corrected one with the
fitted constant (kappa) is NOT used here."""
import os, sys, json
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
from importlib import import_module
T1 = import_module("03_task1_compute")
core = import_module("03_core")
Q, MU, q, H, tau0 = T1.Q, T1.MU, T1.q, T1.H, T1.tau0
res = json.load(open(os.path.join(HERE, "03_task1_results.json")))
tau = {(r["i"], r["j"], r["N"]): r["tauN"] for r in res["pair"] if r.get("tauN")}
Ns = sorted({r["N"] for r in res["pair"] if r.get("tauN")})


def xN(i, N):
    T = tau0 * np.log(N)
    lg = lambda s: (N - 1) * np.log(1 - T * q[s] / N)
    return (lg(0) - lg(i) + np.log(MU[0] / MU[i])) / T


def recon(d, t01, t02, t12):
    w = {}
    for (i, j), t in (((0, 1), t01), ((0, 2), t02), ((1, 2), t12)):
        w[(i, j)] = (H - d[i] + d[j]) / t + 1 / t ** 2
    B = np.diag(d).astype(float)
    for (i, j), x in w.items():
        B[i, j] = B[j, i] = -np.sqrt(x)
    ev, evec = np.linalg.eigh(B)
    h = np.abs(evec[:, 0])
    S = B - ev[0] * np.eye(3)
    return -(S * h[None, :]) / h[:, None]


print("| N | ||Q_N-Q||_2 raw | x log N/loglogN | corrected t/(1-loglogN/(2logN)) ||.||_2 | x log N | ||.|| with x_{i,N} replaced by exact x_i (isolating t error) |")
print("|---:|---:|---:|---:|---:|---:|")
for N in Ns:
    L = np.log(N)
    d = np.array([0.0, xN(1, N), xN(2, N)])
    ts = [tau[(0, 1, N)], tau[(0, 2, N)], tau[(1, 2, N)]]
    Qr = recon(d, *ts)
    e_raw = np.linalg.norm(Qr - Q, 2)
    f = 1 - np.log(L) / (2 * L)
    Qc = recon(d, *[x / f for x in ts])
    e_cor = np.linalg.norm(Qc - Q, 2)
    dtrue = q - q[0]
    e_t = np.linalg.norm(recon(dtrue, *ts) - Q, 2)
    print(f"| {N} | {e_raw:.4f} | {e_raw*L/np.log(L):.3f} | {e_cor:.4f} | {e_cor*L:.3f} | {e_t:.4f} |")
