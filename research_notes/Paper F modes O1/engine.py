# engine.py -- exact law P_N(k) of the plus count of the alternating walk.
# Paper F (problem 131), modal structure (O1).
#
# Coordinates: k = plus steps, j = minus steps.
#   S(k,j) = P(a plus run with law f_+ starts after k plus and j minus steps)
#   E(k,j) = P(a minus run with law f_- starts after k plus and j minus steps)
#   S = S0 + E *_j f_-,   E = E0 + S *_k f_+.
# Seeds: fresh plus S0(0,0)=1; fresh minus E0(0,0)=1; a prepared initial run
# with weights nu_+(d), nu_-(d) gives E0(d,0)=nu_+(d), S0(0,d)=nu_-(d), and the
# atoms Q_+(N) at k=N and Q_-(N) at k=0 (the initial run still running).
# Then P_N(k) = sum_{x<k} S(x,N-k) T_+(k-x) + sum_{j'<N-k} E(k,j') T_-(N-k-j')
#               + Q_+(N) 1{k=N} + Q_-(N) 1{k=0}.
# All sums are of nonnegative terms, in float64.
# Run with: py -I <script that imports this file>
import numpy as np
from scipy.special import zeta as hurwitz


def zeta_law(alpha, nmax, nmin=1):
    """f(n) ~ n^(-alpha-1) on n >= nmin, exact normalization; returns f, T
    with f[n], T[m] = P(X >= m) for 0 <= n, m <= nmax+1."""
    s = alpha + 1.0
    z = hurwitz(s, nmin)
    n = np.arange(nmax + 2, dtype=float)
    f = np.zeros(nmax + 2)
    f[nmin:] = n[nmin:] ** (-s) / z
    T = np.ones(nmax + 2)
    m = np.arange(nmin, nmax + 2, dtype=float)
    T[nmin:] = hurwitz(s, m) / z
    return f, T


def law_from_f(f_head, tail_mass_fn=None):
    """Law given by an explicit mass vector f_head[0..nmax+1] (f_head[0]=0)
    whose total over all n is 1; T[m] = 1 - sum_{n<m} f(n)."""
    f = np.asarray(f_head, dtype=float)
    T = 1.0 - np.concatenate(([0.0], np.cumsum(f)[:-1]))
    T[0] = 1.0
    return f, T


def build(fp, fm, nmax, S0=None, E0=None):
    """Arrays S[k,j], E[k,j] for k+j <= nmax."""
    S = np.zeros((nmax + 1, nmax + 1))
    E = np.zeros((nmax + 1, nmax + 1))
    if S0 is None:
        S0 = np.zeros((nmax + 1, nmax + 1))
    if E0 is None:
        E0 = np.zeros((nmax + 1, nmax + 1))
    fpv = fp[: nmax + 1].copy()
    fpv[0] = 0.0
    fmv = fm[: nmax + 1].copy()
    fmv[0] = 0.0
    for j in range(nmax + 1):
        K = nmax - j + 1  # k = 0..nmax-j
        col = S0[:K, j].copy()
        if j > 0:
            # sum_{y=1}^{j} f_-(y) E[k, j-y]
            col += E[:K, j - 1 :: -1][:, :j] @ fmv[1 : j + 1]
        S[:K, j] = col
        conv = np.convolve(col, fpv[:K])[:K]  # sum_{x} S[k-x,j] f_+(x), x>=1
        E[:K, j] = E0[:K, j] + conv
    return S, E


def law_N(S, E, Tp, Tm, N, Qp=0.0, Qm=0.0):
    """P_N(k), k = 0..N."""
    P = np.zeros(N + 1)
    for k in range(N + 1):
        j = N - k
        v = 0.0
        if k >= 1:
            # sum_{x=0}^{k-1} S[x,j] T_+(k-x)
            v += S[:k, j] @ Tp[k:0:-1]
        if j >= 1:
            # sum_{j'=0}^{j-1} E[k,j'] T_-(j-j')
            v += E[k, :j] @ Tm[j:0:-1]
        P[k] = v
    P[N] += Qp
    P[0] += Qm
    return P


def renewal(f, jmax):
    """u(j), j=0..jmax, renewal mass function of law f."""
    u = np.zeros(jmax + 1)
    u[0] = 1.0
    for j in range(1, jmax + 1):
        u[j] = f[1 : j + 1] @ u[j - 1 :: -1][:j]
    return u


def sign_changes(P, lo=0, hi=None):
    """Indices k (in [lo,hi)) where Delta P changes sign: returns list of k
    such that sign(P[k+1]-P[k]) differs from the previous nonzero sign; the
    reported k is the point between the two differences (a local extremum)."""
    if hi is None:
        hi = len(P) - 1
    d = np.diff(P[lo : hi + 1])
    out = []
    prev = 0
    for i, x in enumerate(d):
        s = 1 if x > 0 else (-1 if x < 0 else 0)
        if s == 0:
            continue
        if prev != 0 and s != prev:
            out.append(lo + i)
        prev = s
    first = None
    for x in d:
        if x != 0:
            first = 1 if x > 0 else -1
            break
    return out, first


def layer_R(fp, Tp, fm, Tm, N, J):
    """Fresh plus start: R[j] = P_N(N-j)/T_+(N) for j = 0..J, computing only
    the columns j <= J of S and E (all k <= N)."""
    K = N + 1
    S = np.zeros((K, J + 1)); E = np.zeros((K, J + 1))
    fpv = fp[:K].copy(); fpv[0] = 0.0
    for j in range(J + 1):
        col = np.zeros(K)
        if j == 0:
            col[0] = 1.0
        else:
            col += E[:, j - 1 :: -1][:, :j] @ fm[1 : j + 1]
        S[:, j] = col
        E[:, j] = np.convolve(col, fpv)[:K]
    R = np.zeros(J + 1)
    for j in range(J + 1):
        k = N - j
        v = S[:k, j] @ Tp[k:0:-1] if k >= 1 else 0.0
        if j >= 1:
            v += E[k, :j] @ Tm[j:0:-1]
        R[j] = v / Tp[N]
    return R


def Cfun(alpha_p, mu_p, u, J):
    """C(j) of Theorem 5.1 (second order in the layer), j = 0..J."""
    v = np.zeros(J + 1)
    for j in range(1, J + 1):
        v[j] = u[:j] @ u[j:0:-1]
    cs = np.concatenate(([0.0], np.cumsum(u[:J])))  # sum_{i<j} u(i)
    jj = np.arange(J + 1)
    return alpha_p * (jj * u[: J + 1] + 2 * mu_p * v + cs)


def layer_R_mixed(fp, Tp, fm, Tm, N, J, wplus=1.0, wminus=0.0):
    """As layer_R, for a start that is fresh plus with weight wplus and fresh
    minus with weight wminus (wplus + wminus = 1)."""
    K = N + 1
    S = np.zeros((K, J + 1)); E = np.zeros((K, J + 1))
    fpv = fp[:K].copy(); fpv[0] = 0.0
    for j in range(J + 1):
        col = np.zeros(K)
        if j == 0:
            col[0] = wplus
        else:
            col += E[:, j - 1 :: -1][:, :j] @ fm[1 : j + 1]
        S[:, j] = col
        E[:, j] = np.convolve(col, fpv)[:K]
        if j == 0:
            E[0, 0] += wminus
    R = np.zeros(J + 1)
    for j in range(J + 1):
        k = N - j
        v = S[:k, j] @ Tp[k:0:-1] if k >= 1 else 0.0
        if j >= 1:
            v += E[k, :j] @ Tm[j:0:-1]
        R[j] = v / Tp[N]
    return R
