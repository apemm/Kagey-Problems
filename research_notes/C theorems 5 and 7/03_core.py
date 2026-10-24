"""Exact finite-horizon machinery for Paper C, Theorem 5 numerics (route T5-C).

Chain: P = I + (T/N) Q, N visits (N-1 transitions), start law mu.
Controlled atom: Pr_mu(n) exp(T v.n / N).

Exact pieces
  * singleton:   mu_i (1 - T q_i/N)^(N-1) e^{T v_i}
  * pair {a,b}:  exact run-count formula, all compositions (n_a, n_b), n_a+n_b=N
  * triple:      exact dynamic programming over (state, counts) for small N, and a
                 capped version (n_k <= L) for larger N
Run as a module via sys.path insertion (py -I does not put the script folder on the path).
"""
import numpy as np
from scipy.special import gammaln
from scipy.special import logsumexp

NEG = -np.inf


def lC(n, k):
    """log binomial(n, k) with -inf outside 0 <= k <= n (arrays broadcast)."""
    n = np.asarray(n, dtype=float)
    k = np.asarray(k, dtype=float)
    ok = (k >= 0) & (k <= n)
    nn = np.where(ok, n, 1.0)
    kk = np.where(ok, k, 0.0)
    out = gammaln(nn + 1) - gammaln(kk + 1) - gammaln(nn - kk + 1)
    return np.where(ok, out, NEG)


# ---------------------------------------------------------------- generators
def reversible_generator(pi, c):
    """Q_ij = c_ij / pi_i, c symmetric with zero diagonal (conductances)."""
    pi = np.asarray(pi, float)
    c = np.asarray(c, float)
    d = len(pi)
    Q = np.zeros((d, d))
    for i in range(d):
        for j in range(d):
            if i != j:
                Q[i, j] = c[i, j] / pi[i]
        Q[i, i] = -Q[i].sum()
    return Q


def class_data(Q, pi):
    """S, R=||S||_2, b = min sqrt(w) over edges, q, w."""
    sq = np.sqrt(pi)
    S = (sq[:, None] * (-Q)) / sq[None, :]
    S = 0.5 * (S + S.T)
    R = np.linalg.norm(S, 2)
    d = len(pi)
    q = -np.diag(Q)
    w = {}
    for i in range(d):
        for j in range(i + 1, d):
            if Q[i, j] > 0:
                w[(i, j)] = Q[i, j] * Q[j, i]
    b = np.sqrt(min(w.values()))
    return S, R, b, q, w


def design_constants(R, b):
    H = 2 * R
    tau0 = 1 / (2 * R)
    U = 8 * R / b ** 2
    M = 4 * R + 4 * U * R ** 2
    return H, tau0, U, M


def limit_t_ij(Q, i, j, H):
    """Pair-entry time of C-I1 with d_i = q_i - q_0 (state 0 is the reference)."""
    q = -np.diag(Q)
    w = Q[i, j] * Q[j, i]
    Dl = (q[i] - q[0]) - (q[j] - q[0])
    s = np.sqrt((H - Dl) ** 2 + 4 * w)
    return (s + H - Dl) / (2 * w)


# ---------------------------------------------------------------- singleton
def log_single(Q, mu, i, N, T, vi):
    q = -Q[i, i]
    x = 1 - T * q / N
    if x <= 0:
        return NEG
    return np.log(mu[i]) + (N - 1) * np.log(x) + T * vi


# ---------------------------------------------------------------- pair
def _both(lPaa, lPbb, lPab, lPba, na, nb, K, lf):
    """log of sum over run counts, both start states.  na, nb: column arrays (floats, integral).
    Returns (log start-a sum, log start-b sum).  lf = table of log n!."""
    r = np.arange(1, K + 1)[None, :]
    na_i = na.astype(np.int64)
    nb_i = nb.astype(np.int64)

    def lc(n_i, kk):
        # log C(n_i - 1, kk) with kk = r-1 or r-2 as int array (broadcast)
        n1 = n_i - 1
        ok = (kk >= 0) & (kk <= n1)
        kc = np.where(ok, kk, 0)
        nc = np.where(ok, n1 - kk, 0)
        out = lf[np.maximum(n1, 0)] - lf[kc] - lf[nc]
        return np.where(ok, out, -np.inf)

    rr = np.arange(1, K + 1)[None, :]
    A1 = lc(na_i, rr - 1)
    A2 = lc(na_i, rr - 2)
    B1 = lc(nb_i, rr - 1)
    B2 = lc(nb_i, rr - 2)
    rf = rr.astype(float)
    # start a:  (r_a = r_b = r) and (r_a = r, r_b = r-1)
    ta1 = A1 + B1 + (na - rf) * lPaa + (nb - rf) * lPbb + rf * lPab + (rf - 1) * lPba
    ta2 = A1 + B2 + (na - rf) * lPaa + (nb - (rf - 1)) * lPbb + (rf - 1) * (lPab + lPba)
    # start b:  (r_b = r_a = r) and (r_b = r, r_a = r-1)
    tb1 = B1 + A1 + (nb - rf) * lPbb + (na - rf) * lPaa + rf * lPba + (rf - 1) * lPab
    tb2 = B1 + A2 + (nb - rf) * lPbb + (na - (rf - 1)) * lPaa + (rf - 1) * (lPab + lPba)
    sa = logsumexp(np.concatenate([ta1, ta2], axis=1), axis=1)
    sb = logsumexp(np.concatenate([tb1, tb2], axis=1), axis=1)
    return sa, sb


_LF = {}


def _lf_table(N):
    if N not in _LF:
        _LF.clear()
        _LF[N] = gammaln(np.arange(N + 2) + 1.0)
    return _LF[N]


def runs_K(Q, a, b, N, T, extra=0):
    qm = max(Q[a, b], Q[b, a])
    mean = T * qm
    return int(min(N // 2 + 2, 4 * mean + 14 * np.sqrt(mean + 1) + 40 + extra))


def log_pair_array(Q, mu, a, b, N, T, K=None, stride=1, nas=None):
    """log Pr_mu(n_a, n_b) for n_a = 1..N-1 (step `stride`), support exactly {a,b}.
    returns (n_a array, log probs)."""
    qa, qb = -Q[a, a], -Q[b, b]
    if T * max(qa, qb) >= N:
        raise ValueError("not stochastic")
    lPaa = np.log(1 - T * qa / N)
    lPbb = np.log(1 - T * qb / N)
    lPab = np.log(T / N * Q[a, b])
    lPba = np.log(T / N * Q[b, a])
    if K is None:
        K = runs_K(Q, a, b, N, T)
    if nas is None:
        nas = np.arange(1, N, stride)
    nas = np.asarray(nas)
    out = np.empty(len(nas))
    lf = _lf_table(N)
    step = max(1, int(3_000_000 // (2 * K)))
    for s0 in range(0, len(nas), step):
        na = nas[s0:s0 + step][:, None].astype(float)
        nb = N - na
        sa, sb = _both(lPaa, lPbb, lPab, lPba, na, nb, K, lf)
        out[s0:s0 + step] = np.logaddexp(sa + np.log(mu[a]), sb + np.log(mu[b]))
    return nas, out


def best_pair(Q, mu, a, b, N, T, va, vb, K=None, stride=1, cache=None):
    """max over compositions of log Pr + T (va n_a + vb n_b)/N ; returns (value, n_a*)."""
    if cache is not None and "arr" in cache:
        nas, lp = cache["arr"]
    else:
        nas, lp = log_pair_array(Q, mu, a, b, N, T, K=K, stride=stride)
        if cache is not None:
            cache["arr"] = (nas, lp)
    tot = lp + T * (va * nas + vb * (N - nas)) / N
    k = int(np.argmax(tot))
    return tot[k], int(nas[k])


# ---------------------------------------------------------------- full 3-state DP
def full3_logprobs(Q, mu, N, T):
    """Exact Pr(n0,n1,n2) for all compositions, 3 states. returns array [n0,n1] (n2 implicit),
    log-scale factor folded in. Practical for N <= ~300."""
    P = np.eye(3) + (T / N) * Q
    assert (P >= -1e-15).all()
    dp = np.zeros((3, N + 2, N + 2))
    for s in range(3):
        n0 = 1 if s == 0 else 0
        n1 = 1 if s == 1 else 0
        dp[s, n0, n1] = mu[s]
    logscale = 0.0
    for t in range(1, N):
        new = np.zeros_like(dp)
        for s2 in range(3):
            acc = P[0, s2] * dp[0] + P[1, s2] * dp[1] + P[2, s2] * dp[2]
            if s2 == 0:
                new[s2, 1:, :] = acc[:-1, :]
            elif s2 == 1:
                new[s2, :, 1:] = acc[:, :-1]
            else:
                new[s2] = acc
        m = new.max()
        new /= m
        logscale += np.log(m)
        dp = new
    tot = dp.sum(axis=0)
    with np.errstate(divide="ignore"):
        return np.log(tot) + logscale


def capped_logprobs(Q, mu, N, T, i, k, L):
    """Exact Pr over compositions with n_k <= L.  Tracks counts of i (0..N) and k (0..L).
    returns array [n_i, n_k] of log Pr (n_j implicit = N - n_i - n_k)."""
    P = np.eye(3) + (T / N) * Q
    assert (P >= -1e-15).all()
    dp = np.zeros((3, N + 2, L + 2))
    for s in range(3):
        dp[s, 1 if s == i else 0, 1 if s == k else 0] = mu[s]
    logscale = 0.0
    for t in range(1, N):
        new = np.zeros_like(dp)
        for s2 in range(3):
            acc = P[0, s2] * dp[0] + P[1, s2] * dp[1] + P[2, s2] * dp[2]
            if s2 == i:
                new[s2, 1:, :] = acc[:-1, :]
            elif s2 == k:
                new[s2, :, 1:] = acc[:, :-1]
            else:
                new[s2] = acc
        new[:, :, L + 1] = 0.0  # discard overflow beyond the cap
        m = new.max()
        new /= m
        logscale += np.log(m)
        dp = new
    tot = dp.sum(axis=0)
    with np.errstate(divide="ignore"):
        return np.log(tot) + logscale


# ---------------------------------------------------------------- spectral scores
def lam_face(S, F, v):
    F = list(F)
    A = S[np.ix_(F, F)] - np.diag([v[x] for x in F])
    return np.linalg.eigvalsh(A)[0]


def leading_scores(S, v, tau):
    """Phi_{tau,v}(F) for all connected faces of a complete 3-state graph (all faces)."""
    import itertools
    out = {}
    d = S.shape[0]
    for r in range(1, d + 1):
        for F in itertools.combinations(range(d), r):
            if r > 1 and not _connected(S, F):
                continue
            out[F] = (r - 1) + tau * lam_face(S, F, v)
    return out


def _connected(S, F):
    F = list(F)
    seen = {F[0]}
    st = [F[0]]
    while st:
        x = st.pop()
        for y in F:
            if y not in seen and S[x, y] != 0:
                seen.add(y)
                st.append(y)
    return len(seen) == len(F)


def best_pair_fast(Q, mu, a, b, N, T, va, vb, full_below=6000, K=None):
    """Same maximum as best_pair; for N > full_below uses a coarse grid of about 4000
    compositions, then refines every composition within +-3 strides of the coarse argmax.
    (The profile n_a -> log Pr + linear term is smooth and unimodal on this scale; the full
    and fast versions are compared in 03_validate_fast.py.)"""
    if N <= full_below:
        nas, lp = log_pair_array(Q, mu, a, b, N, T, K=K)
        tot = lp + T * (va * nas + vb * (N - nas)) / N
        k = int(np.argmax(tot))
        return float(tot[k]), int(nas[k])
    s = max(1, min(N // 4000, int(0.1 * np.sqrt(N / max(T, 1.0)))))
    nas, lp = log_pair_array(Q, mu, a, b, N, T, K=K, stride=s)
    tot = lp + T * (va * nas + vb * (N - nas)) / N
    k = int(np.argmax(tot))
    lo = max(1, int(nas[k]) - 3 * s)
    hi = min(N - 1, int(nas[k]) + 3 * s)
    nas2 = np.arange(lo, hi + 1)
    _, lp2 = log_pair_array(Q, mu, a, b, N, T, K=K, nas=nas2)
    tot2 = lp2 + T * (va * nas2 + vb * (N - nas2)) / N
    k2 = int(np.argmax(tot2))
    return float(tot2[k2]), int(nas2[k2])


# ---------------------------------------------------------------- compositions with exactly one visit to k
def n1_profile(Q, mu, a, b, k, N, T, nas, K=None):
    """log Pr(n_a = nas, n_b = N-1-nas, n_k = 1) exactly, for a retained pair (a,b) and one visit to k.
    Contract the visit to k: the remaining N-1 visits form a path on {a,b}; the visit to k is inserted at the start,
    at the end, or in one of the N-2 gaps, multiplying the path weight by mu_k P_{k,s}/mu_s, P_{e,k}, or
    rho_{xy} = P_{xk} P_{ky} / P_{xy} for a gap of type x->y (requires P_ab, P_ba > 0)."""
    P = np.eye(3) + (T / N) * Q
    Np = N - 1
    nas = np.asarray(nas)
    if K is None:
        K = runs_K(Q, a, b, N, T)
    lPaa, lPbb = np.log(P[a, a]), np.log(P[b, b])
    lPab, lPba = np.log(P[a, b]), np.log(P[b, a])
    rho = {(x, y): P[x, k] * P[k, y] / P[x, y] for x in (a, b) for y in (a, b)}
    lf = _lf_table(N)
    out = np.empty(len(nas))
    step = max(1, int(1_500_000 // (4 * K)))
    for s0 in range(0, len(nas), step):
        na_i = nas[s0:s0 + step][:, None].astype(np.int64)
        nb_i = (Np - na_i)
        na = na_i.astype(float)
        nb = nb_i.astype(float)
        rr = np.arange(1, K + 1)[None, :]
        rf = rr.astype(float)

        def lc(n_i, kk):
            n1 = n_i - 1
            ok = (kk >= 0) & (kk <= n1) & (n1 >= 0)
            kc = np.where(ok, kk, 0)
            nc = np.where(ok, n1 - kk, 0)
            out_ = lf[np.maximum(n1, 0)] - lf[kc] - lf[nc]
            return np.where(ok, out_, -np.inf)
        A1, A2 = lc(na_i, rr - 1), lc(na_i, rr - 2)
        B1, B2 = lc(nb_i, rr - 1), lc(nb_i, rr - 2)
        terms = []
        # A1: start a, end b: a->b r, b->a r-1, stay a na-r, stay b nb-r
        lw = np.log(mu[a]) + A1 + B1 + (na - rf) * lPaa + (nb - rf) * lPbb + rf * lPab + (rf - 1) * lPba
        br = ((na - rf) * rho[(a, a)] + rf * rho[(a, b)] + (rf - 1) * rho[(b, a)] + (nb - rf) * rho[(b, b)]
              + mu[k] * P[k, a] / mu[a] + P[b, k])
        terms.append(lw + np.log(np.maximum(br, 1e-300)))
        # A2: start a, end a: a->b r-1, b->a r-1, stay a na-r, stay b nb-(r-1)
        lw = np.log(mu[a]) + A1 + B2 + (na - rf) * lPaa + (nb - (rf - 1)) * lPbb + (rf - 1) * (lPab + lPba)
        br = ((na - rf) * rho[(a, a)] + (rf - 1) * rho[(a, b)] + (rf - 1) * rho[(b, a)] + (nb - (rf - 1)) * rho[(b, b)]
              + mu[k] * P[k, a] / mu[a] + P[a, k])
        terms.append(lw + np.log(np.maximum(br, 1e-300)))
        # B1: start b, end a: b->a r, a->b r-1, stay b nb-r, stay a na-r
        lw = np.log(mu[b]) + B1 + A1 + (nb - rf) * lPbb + (na - rf) * lPaa + rf * lPba + (rf - 1) * lPab
        br = ((na - rf) * rho[(a, a)] + (rf - 1) * rho[(a, b)] + rf * rho[(b, a)] + (nb - rf) * rho[(b, b)]
              + mu[k] * P[k, b] / mu[b] + P[a, k])
        terms.append(lw + np.log(np.maximum(br, 1e-300)))
        # B2: start b, end b: b->a r-1, a->b r-1, stay b nb-r, stay a na-(r-1)
        lw = np.log(mu[b]) + B1 + A2 + (nb - rf) * lPbb + (na - (rf - 1)) * lPaa + (rf - 1) * (lPab + lPba)
        br = ((na - (rf - 1)) * rho[(a, a)] + (rf - 1) * rho[(a, b)] + (rf - 1) * rho[(b, a)] + (nb - rf) * rho[(b, b)]
              + mu[k] * P[k, b] / mu[b] + P[b, k])
        terms.append(lw + np.log(np.maximum(br, 1e-300)))
        out[s0:s0 + step] = logsumexp(np.concatenate(terms, axis=1), axis=1)
    return out
