# o3_lib.py -- exact face maxima of four reducible faces (block engine), a brute-force
# check of the engine for small N, and the predicted constants from Definition def:tilt.
# Imported by o3_check.py and o3_table.py; not meant to be run by itself.
import math

import numpy as np


def block_best(h, qab, qba, qa, qb, start_a, wa, wb, L):
    """Two-state block {a,b}. For every length l = 0..L return the largest value over
    compositions (k, l-k) with 1 <= k <= l-1 of  wa*P(end a) + wb*P(end b),  where P is
    the probability that the chain (I + hQ) started at a (start_a) or b stays in {a,b}
    for its first l visits with k visits to a and ends in the given state."""
    Pa = np.zeros(L + 2)
    Pb = np.zeros(L + 2)
    if start_a:
        Pa[1] = 1.0
    else:
        Pb[0] = 1.0
    best = np.zeros(L + 1)
    sa, sb, ja, jb = 1 - h * qa, 1 - h * qb, h * qab, h * qba
    for l in range(1, L + 1):
        if l >= 2:
            v = wa * Pa[1:l] + wb * Pb[1:l]
            best[l] = v.max()
        nPa = np.zeros(L + 2)
        nPb = np.zeros(L + 2)
        nPa[1:] = Pa[:-1] * sa + Pb[:-1] * jb
        nPb[:] = Pb * sb + Pa * ja
        Pa, Pb = nPa, nPb
    return best


def face_max(ex, N, T):
    """Exact M_F for example ex in {'E1','E2','E3','E4'}. For E4 also returns the
    length of the block in C1 at the maximizer."""
    h = T / N
    if ex == 'E1':   # {1} -> {2,3}; q12=1, q23=q32=1
        best = block_best(h, 1, 1, 1, 1, True, 1, 1, N)
        n1 = np.arange(1, N - 1)
        vals = (1 - h) ** (n1 - 1) * h * best[N - n1]
        return vals.max()
    if ex == 'E2':   # {1,2} -> {3}; q12=q21=1, q13=1, q34=2
        best = block_best(h, 1, 1, 2, 1, True, 1, 0, N)
        n3 = np.arange(1, N - 1)
        vals = best[N - n3] * h * 1 * (1 - 2 * h) ** (n3 - 1)
        return vals.max()
    if ex == 'E3':   # {1} -> {2,3} -> {4}; q12=1, q23=q32=1, q34=1, q45=3
        best = block_best(h, 1, 1, 1, 2, True, 0, 1, N)
        l = np.arange(2, N - 1)
        m = N - l   # n1 + n4 = m >= 2; log-linear in n1, so the max is at an end
        g = np.maximum((1 - h) ** (m - 2), (1 - 3 * h) ** (m - 2))
        vals = best[l] * h * h * g
        return vals.max()
    if ex == 'E4':   # {1,2} -> {3,4}; q12=q21=1, q13=1, q25=1, q34=q43=1, q35=q45=1
        A = block_best(h, 1, 1, 2, 2, True, 1, 0, N)
        B = block_best(h, 1, 1, 2, 2, True, 1, 1, N)
        l = np.arange(2, N - 1)
        vals = h * A[l] * B[N - l]
        i = int(vals.argmax())
        return vals.max(), int(l[i])
    raise ValueError(ex)


RATES = {
    'E1': (3, {(0, 1): 1, (1, 2): 1, (2, 1): 1}, [0, 1, 2]),
    'E2': (4, {(0, 1): 1, (1, 0): 1, (0, 2): 1, (2, 3): 2}, [0, 1, 2]),
    'E3': (5, {(0, 1): 1, (1, 2): 1, (2, 1): 1, (2, 3): 1, (3, 4): 3}, [0, 1, 2, 3]),
    'E4': (5, {(0, 1): 1, (1, 0): 1, (0, 2): 1, (1, 4): 1, (2, 3): 1, (3, 2): 1,
               (2, 4): 1, (3, 4): 1}, [0, 1, 2, 3]),
}


def brute_face_max(ex, N, T):
    """M_F by a forward recursion over (current state, visit counts) for the full chain
    I + hQ started at state 1, keeping only paths inside F. Independent of block_best."""
    d, rates, F = RATES[ex]
    h = T / N
    q = [0.0] * d
    for (i, j), v in rates.items():
        q[i] += v
    idx = {s: a for a, s in enumerate(F)}
    cur = {}
    c0 = [0] * len(F)
    c0[idx[0]] = 1
    cur[(0, tuple(c0))] = 1.0
    for _ in range(N - 1):
        nxt = {}
        for (s, c), p in cur.items():
            for t in F:
                pr = (1 - h * q[s]) if t == s else h * rates.get((s, t), 0)
                if pr == 0:
                    continue
                cc = list(c)
                cc[idx[t]] += 1
                key = (t, tuple(cc))
                nxt[key] = nxt.get(key, 0.0) + p * pr
        cur = nxt
    tot = {}
    for (s, c), p in cur.items():
        tot[c] = tot.get(c, 0.0) + p
    return max(p for c, p in tot.items() if min(c) > 0)


def predicted_constant(QC, start_w, end_w):
    """(start_w . r)(l . end_w) / ((2 pi)^{(k-1)/2} sqrt(det Sigma)) for the irreducible
    killed matrix QC (k x k), from Definition def:tilt at alpha* (theta = q - lambda)."""
    QC = np.array(QC, float)
    k = QC.shape[0]
    w, V = np.linalg.eig(QC)
    i = int(np.argmax(w.real))
    lam = -w[i].real
    r = np.abs(V[:, i].real)
    wl, U = np.linalg.eig(QC.T)
    j = int(np.argmax(wl.real))
    l = np.abs(U[:, j].real)
    l = l / (l @ r)
    alpha = l * r
    R = np.diag(r)
    Qhat = np.linalg.inv(R) @ (QC + lam * np.eye(k)) @ R
    one = np.ones(k)
    Z = np.linalg.inv(np.outer(one, alpha) - Qhat) - np.outer(one, alpha)
    D = np.diag(alpha)
    G = D @ Z + Z.T @ D
    Sig = G[1:, 1:]
    K = (np.array(start_w) @ r) * (l @ np.array(end_w)) / (
        (2 * math.pi) ** ((k - 1) / 2) * math.sqrt(np.linalg.det(Sig)))
    return lam, alpha, K


def besseli_series(nu, x, terms=400):
    """Modified Bessel function I_nu(x) for integer nu >= 0 by its power series."""
    s, term = 0.0, (x / 2) ** nu / math.gamma(nu + 1)
    for m in range(terms):
        s += term
        term *= (x / 2) ** 2 / ((m + 1) * (m + 1 + nu))
        if term < 1e-18 * s:
            break
    return s
