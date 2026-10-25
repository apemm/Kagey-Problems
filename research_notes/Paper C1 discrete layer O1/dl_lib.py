# dl_lib.py -- shared code for the discrete boundary layer (Paper C1, item O1).
# Exact law by a transfer-matrix recursion, the exact discrete lemma
# (Lemma layer-exact-discrete), the weighted facet functions J_G(beta,z),
# C_G(beta,z) continued to complex z, and the lattice and continuum kernels.
# Paper C1 (problem 131), boundary layer at a facet.
# Library only; the check_*.py scripts import it. Run them with: py -I <script>
import math
import itertools
import numpy as np
from scipy.special import ive


# ----------------------------------------------------------------------------
# Chains
# ----------------------------------------------------------------------------

def make_chain(rates, mu):
    """rates: dict {(a,b): q_ab} on states 0..d-1. Returns (Q, mu) arrays."""
    d = len(mu)
    Q = np.zeros((d, d))
    for (a, b), v in rates.items():
        Q[a, b] = v
    for a in range(d):
        Q[a, a] = -Q[a].sum()
    return Q, np.asarray(mu, dtype=float)


# ----------------------------------------------------------------------------
# Exact law: brute force and transfer-matrix recursion on the face F
# ----------------------------------------------------------------------------

def brute_law(Q, mu, h, F, N):
    """P_N(n) for all n with support inside F, by listing the |F|^N paths."""
    M = np.eye(len(mu)) + h * Q
    out = {}
    for w in itertools.product(F, repeat=N):
        p = mu[w[0]]
        for a, b in zip(w, w[1:]):
            p *= M[a, b]
        n = tuple(w.count(s) for s in F)
        out[n] = out.get(n, 0.0) + p
    return out


def dp_face(Q, mu, h, F, target, read):
    """Transfer-matrix recursion for paths inside F (order of F as given).
    target: max counts per state of F. read: dict step -> list of count tuples.
    Returns dict (step, counts) -> probability of that composition after `step`
    steps (paths that stay in F)."""
    M = (np.eye(len(mu)) + h * Q)[np.ix_(F, F)]
    k = len(F)
    shape = tuple(t + 1 for t in target) + (k,)
    P = np.zeros(shape)
    for a in range(k):
        idx = [0] * k
        idx[a] = 1
        if idx[a] <= target[a]:
            P[tuple(idx) + (a,)] = mu[F[a]]
    out = {}
    last = max(read)
    for step in range(1, last + 1):
        if step in read:
            for c in read[step]:
                out[(step, tuple(c))] = P[tuple(c)].sum()
        if step == last:
            break
        new = np.zeros(shape)
        for b in range(k):
            tmp = P @ M[:, b]  # sum over previous state
            src = [slice(None)] * k
            dst = [slice(None)] * k
            src[b] = slice(0, -1)
            dst[b] = slice(1, None)
            new[tuple(dst) + (b,)] = tmp[tuple(src)]
        P = new
    return out


# ----------------------------------------------------------------------------
# The exact discrete lemma: coefficients of P^{(z)}_{N'}(n-hat)
# ----------------------------------------------------------------------------

def facet_data(Q, mu, F, i):
    """G = F minus i (order kept). Returns G, A_G (off-diagonal rates in G),
    q_G (full exit rates), c_minus, c_plus, mu_G, mu_i."""
    G = [s for s in F if s != i]
    AG = Q[np.ix_(G, G)].copy()
    np.fill_diagonal(AG, 0.0)
    qG = -np.diag(Q)[G]
    cm = Q[G, i].copy()
    cp = Q[i, G].copy()
    return G, AG, qG, cm, cp, mu[G].copy(), mu[i]


def weighted_poly(Q, mu, h, F, i, nhat, Kmax):
    """Coefficients [z^K] P^{(z)}_{N'}(nhat), K = 0..Kmax, by a recursion that
    carries the power of z (Lemma layer-exact-discrete, definition)."""
    G, AG, qG, cm, cp, muG, mui = facet_data(Q, mu, F, i)
    m = len(G)
    M0 = np.eye(m) + h * (AG - np.diag(qG))
    M1 = h * h * np.outer(cm, cp)
    start0, start1 = muG, h * mui * cp
    end0, end1 = np.ones(m), h * cm
    Np = sum(nhat)
    shape = tuple(t + 1 for t in nhat) + (m, Kmax + 1)
    P = np.zeros(shape)
    for a in range(m):
        idx = [0] * m
        idx[a] = 1
        if nhat[a] >= 1:
            P[tuple(idx) + (a, 0)] += start0[a]
            if Kmax >= 1:
                P[tuple(idx) + (a, 1)] += start1[a]
    for step in range(1, Np):
        new = np.zeros(shape)
        for b in range(m):
            tmp = np.tensordot(P, M0[:, b], axes=([m], [0]))  # counts..., K
            tmp1 = np.tensordot(P, M1[:, b], axes=([m], [0]))
            tmp[..., 1:] += tmp1[..., :-1]
            src = [slice(None)] * m
            dst = [slice(None)] * m
            src[b] = slice(0, -1)
            dst[b] = slice(1, None)
            new[tuple(dst) + (b,)] = tmp[tuple(src)]
        P = new
    v = P[tuple(nhat)]  # (m, Kmax+1)
    coef = np.zeros(Kmax + 1)
    for a in range(m):
        coef += end0[a] * v[a]
        coef[1:] += end1[a] * v[a][:-1]
    return coef


def lemma_rhs(coef, ni, h, qi):
    """sum_K binom(ni-1,K-1) (1-h qi)^(ni-K) [z^K] P^{(z)}."""
    p = 1 - h * qi
    return sum(math.comb(ni - 1, K - 1) * p ** (ni - K) * coef[K]
               for K in range(1, min(ni, len(coef) - 1) + 1))


# ----------------------------------------------------------------------------
# Weighted facet functions J_G(beta,z), C_G(beta,z) for complex z
# ----------------------------------------------------------------------------

class Facet:
    """The weighted facet chain Q_G(z) = Q_G + z c^- (c^+)^T of Section 6."""

    def __init__(self, Q, mu, F, i):
        (self.G, self.AG, self.qG, self.cm, self.cp,
         self.muG, self.mui) = facet_data(Q, mu, F, i)
        self.qi = -Q[i, i]
        self.m = len(self.G)
        self._cache = {}

    def A(self, z):
        A = self.AG + z * np.outer(self.cm, self.cp)
        np.fill_diagonal(A, 0.0)
        return A

    def d(self, z):
        return self.qG - z * self.cm * self.cp

    def _newton(self, A, beta, r):
        m = self.m
        for _ in range(60):
            Ar = A @ r
            Fv = (beta / r) @ A - beta * Ar / r ** 2
            Jfull = np.zeros((m, m), dtype=complex)
            for jp in range(m):
                for kk in range(m):
                    val = -beta[kk] * A[kk, jp] / r[kk] ** 2 - beta[jp] * A[jp, kk] / r[jp] ** 2
                    if jp == kk:
                        val += 2 * beta[jp] * Ar[jp] / r[jp] ** 3
                    Jfull[jp, kk] = val
            Fr = Fv[1:]
            Jr = Jfull[1:, 1:]
            dr = np.linalg.solve(Jr, -Fr)
            r = r.copy()
            r[1:] = r[1:] + dr
            if np.max(np.abs(dr)) < 1e-15 * np.max(np.abs(r)):
                break
        return r

    def tilt0(self, beta):
        """Real optimal vector r_beta at z = 0 (r_1 = 1)."""
        key = tuple(np.round(beta, 15))
        if key in self._cache:
            return self._cache[key]
        r = np.ones(self.m, dtype=complex)
        if self.m >= 2:
            # Newton with continuation in beta from the uniform law
            A = self.A(0.0)
            for t in np.linspace(0.0, 1.0, 21)[1:]:
                b = (1 - t) * np.ones(self.m) / self.m + t * beta
                r = self._newton(A, b, r)
        self._cache[key] = r
        return r

    def JC(self, beta, z, steps=24):
        """(J_G(beta,z), C_G(beta,z)) by continuation along [0, z]."""
        m = self.m
        beta = np.asarray(beta, dtype=float)
        r = self.tilt0(beta).copy()
        sq_prev = None
        for t in np.linspace(0.0, 1.0, steps + 1):
            zz = t * z
            A = self.A(zz)
            if m >= 2:
                r = self._newton(A, beta, r)
            theta = (A @ r) / r
            J = np.sum(beta * (self.d(zz) - theta))
            l = beta / r
            if m >= 2:
                Qh = A * r[None, :] / r[:, None] - np.diag(theta)
                Zm = np.linalg.inv(np.outer(np.ones(m), beta) - Qh) - np.outer(np.ones(m), beta)
                D = np.diag(beta)
                Gam = D @ Zm + Zm.T @ D
                det = np.linalg.det(Gam[1:, 1:])
                sq = np.sqrt(det + 0j)
                if sq_prev is not None and abs(sq - sq_prev) > abs(-sq - sq_prev):
                    sq = -sq
                sq_prev = sq
            else:
                sq = 1.0
            mu_z = self.muG + zz * self.mui * self.cp
            e_z = 1 + zz * self.cm
            C = (mu_z @ r) * (l @ e_z) / ((2 * math.pi) ** ((m - 1) / 2) * sq)
        return J, C

    def omega(self, beta):
        r = self.tilt0(np.asarray(beta, float)).real
        l = np.asarray(beta) / r
        return (self.cm @ l) * (self.cp @ r)


class Circle:
    """J_G and C_G sampled on |z| = rho, M points, for a fixed beta."""

    def __init__(self, fac, beta, rho, M=192):
        self.rho = rho
        self.phi = 2 * math.pi * np.arange(M) / M
        self.z = rho * np.exp(1j * self.phi)
        J0, C0 = fac.JC(beta, 0.0)
        self.J0, self.C0 = J0.real, C0.real
        vals = [fac.JC(beta, zz) for zz in self.z]
        self.J = np.array([v[0] for v in vals])
        self.C = np.array([v[1] for v in vals])
        self.qi = fac.qi

    def lam(self, S):
        """Lambda~(z) = C(z)/C(0) exp(S(J(0)-J(z))) on the circle."""
        return self.C / self.C0 * np.exp(S * (self.J0 - self.J))

    def L_lattice(self, n, S, h):
        """(h/2 pi i) oint (1 - h qi + h/z)^(n-1) Lambda~ dz/z^2."""
        w = (1 - h * self.qi + h / self.z) ** (n - 1)
        return (h * np.mean(w * self.lam(S) / self.z)).real

    def K_cont(self, x, S):
        """e^{-qi x} (1/2 pi i) oint e^{x/z} Lambda~ dz/z^2 (Theorem layer)."""
        w = np.exp(x / self.z - self.qi * x)
        return np.mean(w * self.lam(S) / self.z).real


# ----------------------------------------------------------------------------
# Pair face (k = 2): exact formula, Laguerre kernel, continuum (Pedler) kernel
# ----------------------------------------------------------------------------

def pair_constants(qji, qij, muj, mui):
    om = qji * qij
    rho = mui / muj
    return om, [1.0, qji + rho * qij, rho * om]


def pair_exact_ratio(ni, Np, h, qji, qij, qj, qi, muj, mui):
    """R = P_N(n)/P_{N'}(n-hat) for F = {j,i}, exactly (discrete Pedler)."""
    om, c = pair_constants(qji, qij, muj, mui)
    pi_, pj = 1 - h * qi, 1 - h * qj
    tot = 0.0
    for K in range(1, ni + 1):
        a = math.comb(ni - 1, K - 1) * pi_ ** (ni - K)
        s = 0.0
        for e in range(3):
            mm = K - e
            if mm < 0 or mm > Np - 1:
                continue
            s += c[e] * h ** e * math.comb(Np - 1, mm) * (h * h * om / pj) ** mm
        tot += a * s
    return tot


def pair_laguerre(ni, Np, h, qji, qij, qi, muj, mui):
    om, c = pair_constants(qji, qij, muj, mui)
    S = h * Np
    pi_ = 1 - h * qi
    tot = 0.0
    for K in range(1, ni + 1):
        a = math.comb(ni - 1, K - 1) * pi_ ** (ni - K) * h ** K
        s = sum(c[e] * (S * om) ** (K - e) / math.factorial(K - e)
                for e in range(3) if K - e >= 0)
        tot += a * s
    return tot


def pair_bessel(x, S, qji, qij, qi, muj, mui):
    """K(x,S) = f_F(S,x)/f_G(S) for the pair face (Proposition pair-face)."""
    om, c = pair_constants(qji, qij, muj, mui)
    zeta = 2 * math.sqrt(om * S * x)
    sc = math.exp(zeta - qi * x)
    I0, I1 = ive(0, zeta) * sc, ive(1, zeta) * sc
    return (math.sqrt(om * S / x) * I1 + c[1] * I0 + c[2] * math.sqrt(x / (om * S)) * I1)


def pair_bound(ni, Np, h, qji, qij, qj, qi):
    """Explicit two-sided bound on R/L - 1 of the pair-face theorem."""
    om = qji * qij
    S = h * Np
    U = om * S * h * ni / (1 - h * qi)
    lo = -(U + 2 * math.sqrt(U) + 2) / (2 * Np)
    hi = math.exp(2 * h * qj * (1 + 2 * math.sqrt(U))) - 1
    return lo, hi
