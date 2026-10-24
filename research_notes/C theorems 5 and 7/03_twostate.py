"""Two-state counterexample over all starts (outline 11, Section 5).
Q = [[-1,1],[1,-1]], v = (0,1), tau = 1/4, T = tau log N.
Leading scores Phi: {1}: tau*1, {2}: 0, {1,2}: 1 + tau*(1-sqrt5)/2.  Predicted winner {2}.
Exact maximisers: singletons in closed form, pair by the exact run-count formula."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from importlib import import_module
core = import_module("03_core")
Q = np.array([[-1.0, 1.0], [1.0, -1.0]])
v = np.array([0.0, 1.0])
tau = 0.25
S = -Q
print("Leading scores: {1}: %.4f  {2}: %.4f  {1,2}: %.4f" % (
    tau * (1 - 0), tau * (1 - 1), 1 + tau * np.linalg.eigvalsh(S - np.diag(v))[0]))


def faces(N, mu2, with_pair=True):
    T = tau * np.log(N)
    mu = np.array([1 - mu2, mu2])
    f = {"{1}": core.log_single(Q, mu, 0, N, T, 0.0), "{2}": core.log_single(Q, mu, 1, N, T, 1.0)}
    if with_pair:
        val, ns = core.best_pair_fast(Q, mu, 0, 1, N, T, 0.0, 1.0, full_below=3000)
        f["{1,2}"] = val
    return f


print("\nTable A: mu_2 = 1/(1 + c N^(1/4)); log-weights of the three faces and the exact winner")
print("N | c | log w{1} | log w{2} | log w{1,2} | winner | w{2}/w{1}")
for c in (2.0, 1.0, 0.5):
    for N in (10 ** 2, 10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6, 10 ** 7):
        mu2 = 1 / (1 + c * N ** 0.25)
        f = faces(N, mu2)
        win = max(f, key=f.get)
        print(f"{N:.0e} | {c} | {f['{1}']:.4f} | {f['{2}']:.4f} | {f['{1,2}']:.4f} | {win} | {np.exp(f['{2}']-f['{1}']):.4f}")

print("\nTable B: singleton-only winners for c = 2 at huge N (the pair is lower by a power of N, checked above to N=1e7)")
for e in range(2, 41, 4):
    N = 10.0 ** e
    mu2 = 1 / (1 + 2 * N ** 0.25)
    T = tau * np.log(N)
    # (1 - T/N)^(N-1) is common to both singletons
    l1 = np.log(1 - mu2)
    l2 = np.log(mu2) + T
    print(f"N=1e{e} ratio w2/w1 = {np.exp(l2-l1):.6f}")

print("\nTable C: fixed starts, onset N* = smallest N from which {2} stays the exact winner (singletons+pair checked at N<=1e6)")
print("mu_2 | onset N (singletons) | (mu_1/mu_2)^4 | pair ever winning?")
for mu2 in (0.5, 0.2, 0.1, 0.05, 0.02, 0.01, 0.005):
    Ng = np.unique(np.round(10 ** np.linspace(1, 14, 3000)).astype(float))
    wins = []
    for N in Ng:
        T = tau * np.log(N)
        l1 = np.log(1 - mu2)
        l2 = np.log(mu2) + T
        wins.append(l2 > l1)
    wins = np.array(wins)
    last_false = np.where(~wins)[0]
    onset = Ng[last_false[-1] + 1] if len(last_false) else Ng[0]
    pw = False
    for N in (10 ** 2, 10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6):
        f = faces(int(N), mu2)
        if max(f, key=f.get) == "{1,2}":
            pw = True
    print(f"{mu2} | {onset:.3e} | {((1-mu2)/mu2)**4:.3e} | {pw}")
