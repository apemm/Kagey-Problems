"""Figures for Paper C of Problem 131 (face selection and the planar persistent walk).

Run from anywhere:
    python -B make_figures.py                 check the quoted values, then draw every figure
    python -B make_figures.py --recompute     the same, but recompute every cache first
    python -B make_figures.py --only KEY      fill one cache and stop (KEY is cycles40, cycles72,
                                              window, sticky or planar:r,s such as planar:0.5,1.0)

Each figure is sized for one column (3.37 in) or for the text width (6.4 in on letter paper with
1.05 in margins), has no text smaller than 8 pt when included at its natural size, and is written
as vector PDF and 600 dpi PNG next to this script. Colours go light to dark within a sweep and line
styles alternate, so the figures still read in greyscale.

  fig_cycles  (a) the points (lambda_F, |F|-1) of the connected faces of the 6-cycle and the
              lower-left boundary of their hull (Theorem 3.4 and Table 1);
              (b) the support of the exact mode on the 5-cycle against T at N = 40 and 72
  fig_window  (a) the lines l_F(t) of Corollary 5.2 on K_3 with start (1/2, 1/2, 0);
              (b) the ends of the edge window at N = 10^6, ..., 10^20 against (log L)/L
  fig_sticky  the probability of a direct jump for the sticky HDP weak limit on 3 states
              (Proposition 7.4; Paper C no longer includes fig_window or fig_sticky)
  fig_planar  (a) sT*_N - N(1 - p_N) for (r, s) = (0.1, 1) (Theorem 6.4);
              (b) the zero-turn share 2 S_N(u*) at the crossing (Theorem 6.3, Corollary 6.6)

Every plotted number comes from an exact computation. The engines are adapted from the research
scripts named in the paper's verification section:
  C2_dp.py, C2_modes.py, C2_faces.py   composition law of the chain I + hQ by dynamic programming,
                                       the type of the global mode, exit rates of all faces
  C5_engine.py, C5_P6prime.py          run expansion of Lemma 2.3 for one face, K_3 window ends
  C4_hdp.py, C4_hdp_quad.py            Monte Carlo and quadrature for the direct-jump probability
  C3_core.py, C3_run_new.py,           three-level representation (Lemma 6.1) of the origin mass,
  C3_run_big.py                        the planar crossing, Paper A's polynomial S_N
The slow parts are cached in ../data/figdata_*.json. check() compares every plotted headline
number with the value the paper (or its research notes) states and stops with a list of the
disagreements.

Conventions. T = N h throughout, as in the paper. The research script C5_P6prime.py measured the
K_3 window in N u with u = h/(1 - 2h) instead. The crossing is a property of h, so the two values
of t differ by exactly N u - N h = 2 T h/(1 - 2h), which check() takes into account.
"""

from __future__ import annotations

import argparse
import json
import logging
import warnings
from math import comb, cos, exp, lgamma, log, log1p, pi, sqrt
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
logging.getLogger("fontTools").setLevel(logging.ERROR)
import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import IntegrationWarning, quad
from scipy.optimize import brentq, minimize_scalar
from scipy.special import betainc, betaln, gammaln
from scipy.stats import binom

HERE = Path(__file__).resolve().parent
DATA = HERE.parent / "data"
COL, FULL = 3.37, 6.4
LOG2 = log(2.0)
C0 = 0.5 * log(pi / 8)                     # Paper A's constant c_0

plt.rcParams.update({
    "font.size": 8, "axes.labelsize": 8, "legend.fontsize": 8,
    "xtick.labelsize": 8, "ytick.labelsize": 8,
    "font.family": "serif", "mathtext.fontset": "cm",
    "axes.linewidth": 0.6, "lines.linewidth": 1.0,
    "xtick.direction": "in", "ytick.direction": "in",
    "xtick.top": True, "ytick.right": True,
    "savefig.bbox": "tight", "savefig.pad_inches": 0.02,
    "pdf.fonttype": 42,
})


def save(fig, name):
    fig.savefig(HERE / f"{name}.pdf")
    fig.savefig(HERE / f"{name}.png", dpi=600)
    plt.close(fig)
    print(f"wrote {name}.pdf and {name}.png")


# The palette is batlow, from F. Crameri's Scientific colour maps (perceptually
# uniform, readable in grayscale and with color-vision deficiencies). Without
# the package cmcrameri the figures fall back to viridis.
try:
    from cmcrameri import cm as _cmc
    PALETTE = _cmc.batlow
except ImportError:
    PALETTE = plt.get_cmap("viridis")


def shades(n, cmap=None, lo=0.0, hi=0.82):
    """n colours from light to dark."""
    cm = PALETTE if cmap is None else plt.get_cmap(cmap)
    return [cm(x) for x in np.linspace(hi, lo, n)]


def panel(ax, letter, x=0.03, y=0.95):
    ax.text(x, y, f"({letter})", transform=ax.transAxes, va="top")


def cache(name, compute, recompute=False):
    """Load ../data/figdata_<name>.json, or compute it and write it."""
    path = DATA / f"figdata_{name}.json"
    if path.exists() and not recompute:
        return json.loads(path.read_text(encoding="utf-8"))
    data = compute()
    DATA.mkdir(exist_ok=True)
    path.write_text(json.dumps(data, indent=1), encoding="utf-8")
    print(f"wrote {path.name}")
    return data


# ================================================================ 1. cycles

def cycle_rates(d):
    W = np.zeros((d, d))
    for i in range(d):
        W[i, (i + 1) % d] = W[(i + 1) % d, i] = 1.0
    return W


def generator(W):
    Q = np.array(W, dtype=float)
    np.fill_diagonal(Q, 0.0)
    np.fill_diagonal(Q, -Q.sum(axis=1))
    return Q


def connected(W, F):
    seen, stack = {F[0]}, [F[0]]
    while stack:
        i = stack.pop()
        for j in F:
            if j not in seen and W[i][j] != 0:
                seen.add(j)
                stack.append(j)
    return len(seen) == len(F)


def all_faces(W):
    """[(face, lambda_F, connected)] for every face; lambda_F is the least eigenvalue of -Q_F."""
    d = len(W)
    Q = generator(W)
    out = []
    for mask in range(1, 1 << d):
        F = [i for i in range(d) if mask >> i & 1]
        lam = float(np.linalg.eigvalsh(-Q[np.ix_(F, F)]).min())
        out.append((F, max(lam, 0.0), connected(W, F)))
    return out


def lower_left_hull(points):
    """Winners of min tau*lam + y over the points (lam, y), for tau from 0 to infinity.

    Returns the hull vertices in the order they win, [(lam, y)], and the switch values tau
    between consecutive ones (minus the slopes of the hull edges)."""
    best = {}
    for lam, y in points:                      # least exit rate for each size
        best[y] = min(best.get(y, np.inf), lam)
    pts = sorted(best.items())                 # by size y
    hull = []
    for y, lam in pts:                         # lower convex hull in the plane (y, lam)
        while len(hull) >= 2:
            (y0, l0), (y1, l1) = hull[-2], hull[-1]
            if (y1 - y0) * (lam - l0) - (l1 - l0) * (y - y0) <= 1e-12:
                hull.pop()
            else:
                break
        hull.append((y, lam))
    verts = [(hull[0][1], hull[0][0])]
    taus = []
    for (y0, l0), (y1, l1) in zip(hull, hull[1:]):
        if l1 >= l0:                           # only edges exposed by directions (tau, 1)
            break
        taus.append((y1 - y0) / (l0 - l1))
        verts.append((l1, y1))
    return verts, taus


def arc_lambda(k):
    return 2 - 2 * cos(pi / (k + 1))


# ---- exact composition law on the packed simplex (adapted from C2_dp.run_batch)

def binom_table(nmax, rmax):
    B = np.zeros((nmax + 1, rmax + 1), dtype=np.int64)
    for n in range(nmax + 1):
        for r in range(rmax + 1):
            B[n, r] = comb(n, r)
    return B


def composition_law(Q, N, Ts, start=None):
    """probs[M, len(Ts)] and comps[M, d]: P(composition = comps[r]) for P = I + (T/N) Q.

    Compositions of k into d parts are kept in colex rank order, s_i = c_0 + ... + c_i + i and
    rank(c) = sum_i C(s_i, i + 1). The recursion adds one visit at a time."""
    Q = np.asarray(Q, dtype=float)
    d = Q.shape[0]
    Ts = np.atleast_1d(np.asarray(Ts, dtype=float))
    P = np.eye(d)[None] + (Ts / N)[:, None, None] * Q[None]
    if P.min() < -1e-15:
        raise ValueError("negative transition probability")
    Bt = binom_table(N + d, d)
    if start is None:
        start = np.full(d, 1.0 / d)
    comps = np.eye(d, dtype=np.int32)
    S = np.cumsum(comps[:, :d - 1], axis=1) + np.arange(d - 1)
    r = sum(Bt[S[:, i], i + 1] for i in range(d - 1))
    comps = comps[np.argsort(r)]
    A = np.zeros((len(Ts), d, d))
    for idx in range(d):
        j = int(np.argmax(comps[idx]))
        A[:, idx, j] = start[j]
    for k in range(2, N + 1):
        Mk = comb(k + d - 1, d - 1)
        S = np.cumsum(comps[:, :d - 1], axis=1) + np.arange(d - 1)
        V = np.matmul(A, P)
        B = np.zeros((len(Ts), Mk, d))
        new = np.zeros((Mk, d), dtype=np.int32)
        for j in range(d):
            r = np.zeros(len(comps), dtype=np.int64)
            for i in range(d - 1):
                r += Bt[S[:, i] + (1 if i >= j else 0), i + 1]
            B[:, r, j] = V[:, :, j]
            new[r] = comps
            new[r, j] += 1
        A, comps = B, new
    return A.sum(axis=2).T, comps


def cycle_type(mask, d):
    s = bin(mask).count("1")
    if s == d:
        return f"full{d}"
    bits = [(mask >> i) & 1 for i in range(d)]
    runs = sum(1 for i in range(d) if bits[i] and not bits[i - 1])
    return f"arc{s}" if runs == 1 else f"nonarc{s}"


class ModeTyper:
    """The support type of the global mode of the composition on the d-cycle."""

    def __init__(self, d, N, batch=4):
        self.Q, self.N, self.d, self.batch = generator(cycle_rates(d)), N, d, batch
        self.groups = None

    def __call__(self, Ts):
        out = []
        Ts = np.atleast_1d(np.asarray(Ts, dtype=float))
        for b in range(0, len(Ts), self.batch):
            probs, comps = composition_law(self.Q, self.N, Ts[b:b + self.batch])
            if self.groups is None:
                masks = ((comps > 0) * (1 << np.arange(self.d))).sum(axis=1)
                types = np.array([cycle_type(int(m), self.d) for m in masks])
                self.groups = {t: np.nonzero(types == t)[0] for t in np.unique(types)}
                self.comps = comps
            for t in range(probs.shape[1]):
                col = probs[:, t]
                best = sorted(((col[idx].max(), ty, int(idx[np.argmax(col[idx])]))
                               for ty, idx in self.groups.items()), reverse=True)
                (p1, ty, j), (p2, ty2, _) = best[0], best[1]
                out.append(dict(T=float(Ts[b + t]), type=ty, comp=[int(x) for x in self.comps[j]],
                                runner_up=ty2, margin=float(np.log10(p1 / p2))))
        return out


def compute_cycles(N, d=5, Tmax=16.0, step=0.2, tol=1e-7):
    """Mode type on a grid of T, and every change of type located by repeated 5-section."""
    typer = ModeTyper(d, N)
    grid = np.round(np.arange(step, Tmax + step / 2, step), 10)
    res = typer(grid)
    trans = []
    for r0, r1 in zip(res, res[1:]):
        if r0["type"] == r1["type"]:
            continue
        a, b = r0["T"], r1["T"]
        while b - a > tol:
            for r in typer(np.linspace(a, b, 6)[1:-1]):
                if r["type"] == r0["type"]:
                    a = r["T"]
                else:
                    b = r["T"]
                    break
        after = typer([b])[0]
        trans.append(dict(lo=a, hi=b, before=r0["type"], after=r1["type"], mode_after=after["comp"]))
    return dict(N=N, d=d, grid=[r["T"] for r in res], types=[r["type"] for r in res],
                modes=[r["comp"] for r in res], margins=[r["margin"] for r in res], transitions=trans)


# ================================================================ 2. the K_3 window

class Face:
    """Run expansion of Lemma 2.3 on one face (adapted from C5_engine.Face).

    W(m) sums mu_{c_1} prod a_{c_j c_{j+1}} over words in F with m_i runs of state i, and
    P_N(n) = sum_m W(m) h^{M-1} prod_i C(n_i - 1, m_i - 1) (1 - h q_i)^{n_i - m_i}."""

    def __init__(self, A, q, mu, mmax):
        A = np.asarray(A, dtype=float)
        self.k = k = A.shape[0]
        self.q, self.mu, self.mmax = np.asarray(q, float), np.asarray(mu, float), mmax
        self.s = s = A.max() if A.max() > 0 else 1.0
        As = A / s
        shape = (mmax + 1,) * k
        size = (mmax + 1) ** k
        coords = np.array(np.unravel_index(np.arange(size), shape), dtype=np.int32)
        tot = coords.sum(0)
        strides = [(mmax + 1) ** (k - 1 - j) for j in range(k)]
        W = np.zeros((k, size))
        for j in range(k):
            e = [0] * k
            e[j] = 1
            W[j, np.ravel_multi_index(e, shape)] = self.mu[j]
        order = np.argsort(tot, kind="stable")
        bounds = np.searchsorted(tot[order], np.arange(k * mmax + 2))
        for M in range(2, k * mmax + 1):
            layer = order[bounds[M]:bounds[M + 1]]
            for j in range(k):
                sel = layer[coords[j, layer] >= 1]
                acc = np.zeros(len(sel))
                for i in range(k):
                    if As[i, j] != 0:
                        acc += As[i, j] * W[i, sel - strides[j]]
                W[j, sel] = acc
        self.Wsc = W.sum(0).reshape(shape)

    def logP(self, n, h):
        m = np.arange(self.mmax + 1)
        jj = np.arange(1, self.mmax + 1, dtype=float)
        vecs = []
        for i in range(self.k):
            ni = n[i]
            v = np.full(self.mmax + 1, -np.inf)
            ok = (m >= 1) & (m <= ni)
            mm = m[ok]
            cl = np.concatenate([[0.0], np.cumsum(np.log(np.maximum(ni - jj, 1e-300)))])
            v[ok] = (mm * log(h * self.s) + cl[mm - 1] - gammaln(mm) + (ni - mm) * np.log1p(-h * self.q[i]))
            vecs.append(v)
        shifts = [np.max(v[np.isfinite(v)]) for v in vecs]
        X = self.Wsc
        for v, sh in zip(vecs, shifts):
            X = np.tensordot(X, np.where(np.isfinite(v), np.exp(v - sh), 0.0), axes=([0], [0]))
        return log(float(X)) + sum(shifts) - log(h * self.s)


K3_MU = (0.5, 0.5, 0.0)
K_FULL = 3 ** 2.5 / (4 * pi)                    # K_[3] of Corollary 4.11 (the K_3 example of Corollary 5.2)


def k3_lines(t, mu=K3_MU):
    """The lines l_F(t) of Theorem 4.8 for the admissible faces of K_3 with start mu."""
    out = {}
    for i in range(3):
        if mu[i] > 0:
            out[(i,)] = log(mu[i]) - 2 * np.asarray(t)
    for i in range(3):
        for j in range(i + 1, 3):
            if mu[i] + mu[j] > 0:
                out[(i, j)] = log((mu[i] + mu[j]) * sqrt(2 / pi)) - np.asarray(t)
    out[(0, 1, 2)] = log(K_FULL) + 0 * np.asarray(t)
    return out


def window_limits():
    t_ve = 0.5 * log(pi / 8)
    t_ef = 0.5 * log(2 / pi) - log(K_FULL)
    return t_ve, t_ef


def compute_window(exponents=range(6, 21, 2)):
    """Ends of the edge window of Corollary 5.2 at N = 10^e, from the exact face maxima."""
    A2 = np.array([[0.0, 1.0], [1.0, 0.0]])
    A3 = np.ones((3, 3)) - np.eye(3)
    edge = Face(A2, [2, 2], [0.5, 0.5], mmax=300)
    full = Face(A3, [2, 2, 2], [0.5, 0.5, 0.0], mmax=120)
    rows = []
    for e in exponents:
        N = 10 ** e
        L = log(N)
        h_of = lambda t: (L - 0.5 * log(L) + t) / N                     # T = N h
        vertex = lambda h: log(0.5) + (N - 1) * log1p(-2 * h)
        edge12 = lambda h: edge.logP([float(N // 2), float(N - N // 2)], h)

        def full_max(h):
            f = lambda c: -full.logP([(N - c) / 2, (N - c) / 2, c], h)
            r = minimize_scalar(f, bounds=(0.1 * N, 0.5 * N), method="bounded", options=dict(xatol=1e-7 * N))
            return -r.fun

        t_ve = brentq(lambda t: edge12(h_of(t)) - vertex(h_of(t)), -3, 2, xtol=1e-12)
        t_ef = brentq(lambda t: full_max(h_of(t)) - edge12(h_of(t)), -3, 2, xtol=1e-10)
        t_ve3 = third_order_tve(L)
        rows.append(dict(N=f"1e{e}", L=L, t_ve=t_ve, t_ef=t_ef, t_ve_third=t_ve3,
                         T_ve=N * h_of(t_ve), T_ef=N * h_of(t_ef)))
        print(f"  window N=1e{e}: t_ve={t_ve:+.6f} t_ef={t_ef:+.6f} third-order t_ve={t_ve3:+.6f}")
    return rows


def third_order_tve(L):
    """t with T + (1/2) log T = L + c_0 + 1/(8T), T = L - (1/2) log L + t."""
    T = brentq(lambda T: T + 0.5 * log(T) - L - C0 - 1 / (8 * T), 0.5, 2 * L + 10, xtol=1e-14)
    return T - L + 0.5 * log(L)


# ================================================================ 3. sticky HDP

HDP_LIMIT = 3 * sqrt(3) / (8 * pi)
MC_OMEGAS = [0.01, 0.1, 1, 3, 10, 30, 100, 1000]
QUAD_OMEGAS = [100, 300, 1000, 3000, 30000]


def hdp_monte_carlo(M=10 ** 6, seed=20260925):
    """P(direct jump) by Monte Carlo, exactly as in C4_hdp.py (same seed and order of draws).

    Rows of the kernel are independent, B_j ~ Beta(omega/3, omega/3), and the jump is direct
    iff B1 B2 <= 1/4, (1 - B1) B3 <= 1/4 and (1 - B2)(1 - B3) <= 1/4 (Corollary 7.3(b))."""
    rng = np.random.default_rng(seed)
    out = []
    for om in MC_OMEGAS:
        a = om / 3
        B1, B2, B3 = rng.beta(a, a, size=(3, M))
        direct = (B1 * B2 <= 0.25) & ((1 - B1) * B3 <= 0.25) & ((1 - B2) * (1 - B3) <= 0.25)
        P = float(direct.mean())
        out.append(dict(omega=om, P=P, se=sqrt(P * (1 - P) / M)))
    return out


def hdp_quadrature(omega):
    """P(direct jump) by adaptive quadrature (route 1 of C4_hdp_quad.py)."""
    a = omega / 3.0
    lb = betaln(a, a)
    W = min(0.5, 16 / (2 * sqrt(2 * a + 1)))
    f = lambda b: np.exp((a - 1) * (np.log(b) + np.log1p(-b)) - lb)
    F = lambda b: betainc(a, a, b)

    def inner(b1):
        U = min(1.0, 1 / (4 * (1 - b1)))
        hi2 = min(1.0, 1 / (4 * b1))
        lo2 = 0.0 if U >= 1 else max(0.0, 1 - 1 / (4 * (1 - U)))
        if hi2 <= lo2:
            return 0.0
        FU = F(U)
        g = lambda b2: f(b2) * max(0.0, FU - F(max(0.0, 1 - 1 / (4 * (1 - b2)))))
        return f(b1) * quad(g, lo2, hi2, epsabs=0, epsrel=1e-12, limit=200)[0]

    with warnings.catch_warnings():
        warnings.simplefilter("ignore", IntegrationWarning)
        return quad(inner, 0.5 - W, 0.5 + W, points=[0.5], epsabs=0, epsrel=1e-11, limit=400)[0]


def compute_sticky():
    mc = hdp_monte_carlo()
    qd = [dict(omega=om, P=hdp_quadrature(om)) for om in QUAD_OMEGAS]
    return dict(monte_carlo=mc, quadrature=qd)


# ================================================================ 4. planar walk

def logC(n, k):
    if k < 0 or k > n or n < 0:
        return -np.inf
    return lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1)


def logS(N, u):
    """log S_N(u) = log sum_j W(N, N/2, j) u^j (Paper A, N even)."""
    a = N // 2
    b = N - a
    lu = log(u)
    terms = []
    for m in range(1, a + 1):
        terms.append(LOG2 + logC(a - 1, m - 1) + logC(b - 1, m - 1) + (2 * m - 1) * lu)
        x1, x2 = logC(a - 1, m) + logC(b - 1, m - 1), logC(a - 1, m - 1) + logC(b - 1, m)
        mx = max(x1, x2)
        if mx > -np.inf:
            terms.append(mx + log(exp(x1 - mx) + exp(x2 - mx)) + 2 * m * lu)
    terms = np.array(terms)
    mx = terms.max()
    return mx + log(np.exp(terms - mx).sum())


def paperA_nq(N):
    """N(1 - p_N) = N u_N/(1 + u_N), with u_N the root of S_N(u) = 1 (Paper A, Thm 5.1)."""
    u = brentq(lambda u: logS(N, u), 1e-10, 1.0, xtol=1e-15)
    return N * u / (1 + u)


def log_corner(N, r, s, h):
    return log(0.25) + (N - 1) * log1p(-(2 * r + s) * h)


def skeleton_law(r, s, Mmax):
    """For m = 0..Mmax the law of the numbers of E, W, N, S runs of a skeleton with m switches,
    started at E (all the functionals used are invariant under the dihedral group)."""
    beta = 2 * r + s
    moves = [(1, r / beta), (-1, r / beta), (2, s / beta)]
    S = Mmax + 2
    cur = np.zeros((4, S, S, S))
    cur[0, 1, 0, 0] = 1.0
    out = []
    for t in range(Mmax + 1):
        if t > 0:
            new = np.zeros_like(cur)
            for z in range(4):
                for dz, p in moves:
                    if p == 0:
                        continue
                    z2 = (z + dz) % 4
                    if z2 == 0:
                        new[z2, 1:, :, :] += p * cur[z][:-1, :, :]
                    elif z2 == 2:
                        new[z2, :, 1:, :] += p * cur[z][:, :-1, :]
                    elif z2 == 1:
                        new[z2, :, :, 1:] += p * cur[z][:, :, :-1]
                    else:
                        new[z2] += p * cur[z]
            cur = new
        marg = cur.sum(axis=0)
        idx = np.argwhere(marg > 0)
        a, b, c = idx[:, 0], idx[:, 1], idx[:, 2]
        d = t + 1 - a - b - c
        keep = d >= 0
        out.append((a[keep], b[keep], c[keep], d[keep], marg[a[keep], b[keep], c[keep]]))
    return out


def threelevel_tables(N, skel, chunk):
    """E0[m], E4[m]: expected count ratio of skeletons with m switches that return to the origin,
    split into zero-turn skeletons and skeletons using all four directions (Lemma 6.1)."""
    n = N // 2
    Mmax = len(skel) - 1
    X = np.arange(n + 1)
    lcc = np.full((Mmax + 2, n + 1), -np.inf)       # log #(compositions of X into k parts)
    lcc[0, 0] = 0.0
    for k in range(1, Mmax + 2):
        v = X >= k
        lcc[k, v] = gammaln(X[v]) - gammaln(k) - gammaln(X[v] - k + 1)
    lccr = lcc[:, ::-1]
    E0, E4 = np.zeros(Mmax + 1), np.zeros(Mmax + 1)
    for m in range(min(Mmax, N - 1) + 1):
        a, b, c, d, pr = skel[m]
        lCm = logC(N - 1, m)
        zt = ((a == 0) & (b == 0)) | ((c == 0) & (d == 0))
        vals = np.zeros(a.size)
        for c0 in range(0, a.size, chunk):
            sl = slice(c0, c0 + chunk)
            v = lcc[a[sl]] + lcc[b[sl]] + lccr[c[sl]] + lccr[d[sl]]
            mx = v.max(axis=1)
            ok = np.isfinite(mx)
            res = np.zeros(v.shape[0])
            res[ok] = np.exp(mx[ok] - lCm) * np.exp(v[ok] - mx[ok, None]).sum(axis=1)
            vals[sl] = res
        E0[m], E4[m] = (pr * vals)[zt].sum(), (pr * vals)[~zt].sum()
    return E0, E4


def origin_parts(N, r, s, h, E0, E4):
    w = binom.pmf(np.arange(len(E0)), N - 1, (2 * r + s) * h)
    return float((w * E0).sum()), float((w * E4).sum()), float(binom.sf(len(E0) - 1, N - 1, (2 * r + s) * h))


PLANAR_NS = [40, 80, 160, 320, 640, 1280, 2560, 5120, 10240]
PLANAR_PAIRS = {(0.1, 1.0): PLANAR_NS, (0.3, 1.0): PLANAR_NS[:5], (0.5, 1.0): PLANAR_NS,
                (1.0, 1.0): PLANAR_NS, (1.0, 0.0): PLANAR_NS}


def compute_planar(r, s):
    """The crossing o_N = c_N (unique by Proposition 6.2) and the shares at it, for each N.

    As in the research runs, N <= 640 uses 80 switches and the bracket [0.05, 2.5] x 2L/beta,
    and N >= 1280 uses 70 switches and [0.2, 1.5] x 2L/beta. The neglected tail is printed."""
    beta = 2 * r + s
    rows = []
    skel = {80: skeleton_law(r, s, 80), 70: skeleton_law(r, s, 70)}
    for N in PLANAR_PAIRS[(r, s)]:
        small = N <= 640
        mmax = 80 if small else 70
        E0, E4 = threelevel_tables(N, skel[mmax], chunk=20000 if small else max(200, 4000000 // (N // 2 + 1)))
        f = lambda T: log(sum(origin_parts(N, r, s, T / N, E0, E4)[:2])) - log_corner(N, r, s, T / N)
        Tg = 2 * log(N) / beta
        lo, hi = (0.05, 2.5) if small else (0.2, 1.5)
        T = brentq(f, lo * Tg, hi * Tg, xtol=1e-13, rtol=1e-14)
        h = T / N
        z, f4, tail = origin_parts(N, r, s, h, E0, E4)
        corner = exp(log_corner(N, r, s, h))
        S2 = 2 * exp(logS(N, s * h / (1 - beta * h))) if s > 0 else 0.0
        row = dict(N=N, T=T, zero_turn=z / corner, four_dir=f4 / corner, S2=S2, tail=tail / corner)
        if (r, s) == (0.1, 1.0):
            row["nq"] = paperA_nq(N)
        rows.append(row)
        print(f"  planar (r,s)=({r},{s}) N={N}: T*={T:.8f} 2S_N(u*)={S2:.8f} zero-turn={z / corner:.8f} "
              f"tail/corner={tail / corner:.1e}", flush=True)
    return rows


def planar_key(r, s):
    return f"planar_{r:g}_{s:g}".replace(".", "p")


# ================================================================ data

def load_all(recompute=False):
    D = {}
    D["cycles"] = {N: cache(f"cycles{N}", lambda N=N: compute_cycles(N), recompute) for N in (40, 72)}
    D["window"] = cache("window", compute_window, recompute)
    D["sticky"] = cache("sticky", compute_sticky, recompute)
    D["planar"] = {}
    for (r, s) in PLANAR_PAIRS:
        if s == 0:          # u = 0, so 2 S_N(u*) = 0 exactly and no crossing is needed
            D["planar"][(r, s)] = [dict(N=N, S2=0.0) for N in PLANAR_PAIRS[(r, s)]]
        else:
            D["planar"][(r, s)] = cache(planar_key(r, s), lambda r=r, s=s: compute_planar(r, s), recompute)
    return D


# ================================================================ checks

# The values below are the ones stated in the paper or in its research notes (sec_examples.tex, sec_sticky.tex, Table 1)
# or, for the planar section and the finer data, in the outline and the research notes it cites
# (C2_cell_C5.txt, C5_P6_out.txt, C5_P6prime_out.txt, C4.md, C4_hdp_quad_out.txt, C3.md
# Sections 4.5 and 4.7, C3_run_new.txt, C3_reproduce.txt). Strings keep the quoted digits.

PAPER = {
    "lambda_k": {2: "1", 3: "0.585786", 4: "0.381966", 5: "0.267949"},
    "C6_switches": ["1", "2.414214", "4.906280", "5.236068"],        # 1, 1 + sqrt 2, tau_4, 3 + sqrt 5
    "C6_winners": [1, 2, 3, 4, 6],
    "b_k": {2: "-0.4673558", 3: "-0.9379218"},
    "C5_tau_full": "3.414214",                                          # 2 + sqrt 2
    "C5_transitions": {40: ["2.538112", "5.122981", "6.883528"], 72: ["3.077562", "6.389394", "8.601750"]},
    "C5_order": ["arc1", "arc2", "arc3", "full5"],
    "C5_modes_40": [[20, 20, 0, 0, 0], [9, 22, 9, 0, 0], [8, 8, 8, 8, 8]],
    "C5_N40_text": {"second_order_3": "5.07", "exact_3": "5.12", "first_order_3": "8.91"},
    "window_limits": ["-0.4673558", "-0.4412978"],
    "window_width": "0.0260580",
    "window_ratio": "0.97428",
    "window_N": {                     # (t_ve, t_ef) in the N u convention of C5_P6prime.py
        "1e6": ["-0.390915", "-0.369274"], "1e8": ["-0.406371", "-0.383638"],
        "1e10": ["-0.416276", "-0.392833"], "1e12": ["-0.423230", "-0.399323"],
        "1e14": ["-0.428404", "-0.404171"], "1e16": ["-0.432415", "-0.407943"],
        "1e18": ["-0.435624", "-0.410967"], "1e20": ["-0.438254", "-0.413451"]},
    "window_1e20_text": ["-0.43825", "-0.41345", "0.02480"],
    "window_third_order_gap_1e20": 2e-5,
    # Monte Carlo values as printed by C4_hdp.py (data/ledger_C4.md). The outline and C4.md list
    # 0.2474 at omega = 0.01, which rounds the printed 0.24735 a second time. The estimate itself
    # is 0.247349, so to 4 places it is 0.2473.
    "mc": {0.01: "0.24735", 0.1: "0.22516", 1: "0.11530", 3: "0.05339", 10: "0.01883", 30: "0.00663",
           100: "0.00201", 1000: "0.00021"},
    "mc_text": {"P_1": "0.115", "one_minus_P_1": "0.88"},
    "quad_omegaP": {100: "0.204496", 300: "0.205981", 1000: "0.206517", 3000: "0.206671", 30000: "0.206741"},
    "hdp_limit": "0.2067483",
    "hdp_next_term": "-1.125",                                          # the -9/8 of the numerical next term
    "planar_sT": [
        "2.137184", "2.709238", "3.307795", "3.922798", "4.548265", "5.180877", "5.818846", "6.461180", "7.107271"],
    "planar_gap": ["-0.5729", "-0.5978", "-0.6138", "-0.6243", "-0.6317", "-0.6373", "-0.6419", "-0.6458", "-0.6493"],
    "planar_curve": ["-0.5992", "-0.6141", "-0.6249", "-0.6331", "-0.6395", "-0.6447", "-0.6490", "-0.6526", "-0.6556"],
    "planar_T": {
        (0.3, 1.0): ["2.0493720", "2.6254217", "3.2329623", "3.8591484", "4.4959627"],
        (0.5, 1.0): ["1.921659", "2.474789", "3.062736", "3.672591", "4.2960095",
                     "4.92810714", "5.56619750", "6.20883595", "6.85521855"],
        (1.0, 1.0): ["1.523236", "1.938717", "2.372095", "2.813578", "3.2577636",
                     "3.70221925", "4.14615113", "4.58951666", "5.03254083"]},
    # zero-turn share 2 S_N(u*); from N = 1280 on the notes give the EW share S_N(u*), which is doubled
    "planar_share": {
        (0.1, 1.0): ["0.98627", "0.98861", "0.99126", "0.99366", "0.9955879",
                     ("0.49851428", 2), ("0.49902412", 2), ("0.49937155", 2), ("0.49960168", 2)],
        (0.3, 1.0): ["0.9285153", "0.9298968", "0.9355268", "0.9434387", "0.9521065"],
        (0.5, 1.0): ["0.81799", "0.79678", "0.78263", "0.77379", "0.7686739",
                     ("0.38301378", 2), ("0.38245982", 2), ("0.38235717", 2), ("0.38249980", 2)],
        (1.0, 1.0): ["0.49419", "0.41262", "0.34317", "0.28431", "0.2346652",
                     ("0.09648150", 2), ("0.07905091", 2), ("0.06455176", 2), ("0.05255050", 2)]},
    "switch_limit": "0.774852",
}


def half_ulp(s):
    """Half a unit in the last quoted place of the decimal string s."""
    return 0.5 * 10.0 ** -(len(s.split(".")[1]) if "." in s else 0)


def check(D):
    bad = []

    def cmp(label, got, quoted, tol=None, factor=1):
        want = float(quoted) * factor
        tol = (half_ulp(quoted) * factor if tol is None else tol) + 1e-12
        if not abs(got - want) <= tol:
            bad.append(f"{label}: stated {quoted}{'' if factor == 1 else f' (x{factor})'}, computed {got:.8g}")

    # ---- Figure 4(a) and Table 1: the hull of the 6-cycle from all 63 faces
    faces = all_faces(cycle_rates(6))
    conn = [(lam, len(F) - 1) for F, lam, c in faces if c]
    if len(conn) != 31:
        bad.append(f"C_6: {len(conn)} connected faces, expected 30 arcs and the cycle")
    for F, lam, c in faces:
        k = len(F)
        if c and k < 6 and abs(lam - arc_lambda(k)) > 1e-12:
            bad.append(f"C_6 arc {F}: lambda {lam} is not 2 - 2cos(pi/(k+1))")
        if not c:                              # a face that is not an arc: it costs more than its longest arc
            longest = max(len(comp) for comp in arc_components(F, 6))
            if abs(lam - arc_lambda(longest)) > 1e-12:
                bad.append(f"C_6 face {F}: lambda {lam} is not that of its longest arc")
    verts, taus = lower_left_hull(conn)
    if [y + 1 for _, y in verts] != PAPER["C6_winners"]:
        bad.append(f"C_6 winners: sizes {[y + 1 for _, y in verts]}, stated {PAPER['C6_winners']}")
    for i, (got, q) in enumerate(zip(taus, PAPER["C6_switches"])):
        cmp(f"C_6 switch value {i + 1}", got, q)
    for k, q in PAPER["lambda_k"].items():
        cmp(f"lambda_{k}", arc_lambda(k), q)
    cmp("tau_4 closed form", 2 / (1 - 2 * sqrt(2) + sqrt(5)), PAPER["C6_switches"][2])
    cmp("tau_full(C_6) = 3 + sqrt 5", 2 / arc_lambda(4), PAPER["C6_switches"][3])
    cmp("tau_full(C_5) = 2 + sqrt 2", 2 / arc_lambda(3), PAPER["C5_tau_full"])
    for k, q in PAPER["b_k"].items():
        cmp(f"b_{k}", b_k(k), q)

    # ---- Figure 4(b): the exact mode on C_5
    for N, qs in PAPER["C5_transitions"].items():
        C = D["cycles"][N]
        seq = [t for i, t in enumerate(C["types"]) if i == 0 or t != C["types"][i - 1]]
        if seq != PAPER["C5_order"]:
            bad.append(f"C_5, N={N}: mode types {seq}, stated {PAPER['C5_order']}")
        tr = C["transitions"]
        if len(tr) != len(qs):
            bad.append(f"C_5, N={N}: {len(tr)} changes of the mode, stated {len(qs)}")
        for t, q in zip(tr, qs):
            cmp(f"C_5, N={N}, {t['before']} -> {t['after']}", 0.5 * (t["lo"] + t["hi"]), q, tol=2e-6)
    for t, q in zip(D["cycles"][40]["transitions"], PAPER["C5_modes_40"]):
        if sorted(t["mode_after"]) != sorted(q):
            bad.append(f"C_5, N=40: mode after {t['before']} is {t['mode_after']}, stated {q}")
    L40 = log(40)
    txt = PAPER["C5_N40_text"]
    cmp("C_5, N=40, tau_3 (L - log(L)/2 + b_3)", (1 + sqrt(2)) * (L40 - 0.5 * log(L40) + b_k(3)), txt["second_order_3"])
    cmp("C_5, N=40, exact switch 2 -> 3", 0.5 * sum(D["cycles"][40]["transitions"][1][k] for k in ("lo", "hi")),
        txt["exact_3"])
    cmp("C_5, N=40, tau_3 log N", (1 + sqrt(2)) * L40, txt["first_order_3"])

    # ---- fig_window, the K_3 window (no longer included in Paper C)
    t_ve, t_ef = window_limits()
    cmp("K_3 window, left limit", t_ve, PAPER["window_limits"][0])
    cmp("K_3 window, right limit", t_ef, PAPER["window_limits"][1])
    cmp("K_3 window, width", t_ef - t_ve, PAPER["window_width"])
    cmp("K_3 criterion ratio", (3 ** 2.5 / 8 * 0.5), PAPER["window_ratio"])
    lines = k3_lines(np.array([0.5 * (t_ve + t_ef)]))
    top = max(lines, key=lambda F: lines[F][0])
    if top != (0, 1):
        bad.append(f"K_3: the top line inside the window is {top}, not the edge {{1,2}}")
    for row in D["window"]:
        q = PAPER["window_N"][row["N"]]
        for end, qq in zip(("ve", "ef"), q):
            T = row[f"T_{end}"]
            N = float(row["N"])
            h = T / N
            shift = 2 * T * h / (1 - 2 * h)          # N u - N h at the same crossing h
            cmp(f"K_3 window, N={row['N']}, t_{end} (N u convention)", row[f"t_{end}"] + shift, qq)
    r20 = next(r for r in D["window"] if r["N"] == "1e20")
    cmp("K_3 window, N=1e20, left end", r20["t_ve"], PAPER["window_1e20_text"][0])
    cmp("K_3 window, N=1e20, right end", r20["t_ef"], PAPER["window_1e20_text"][1])
    cmp("K_3 window, N=1e20, width", r20["t_ef"] - r20["t_ve"], PAPER["window_1e20_text"][2])
    gap = abs(r20["t_ve"] - r20["t_ve_third"])
    if not round(gap, 5) <= PAPER["window_third_order_gap_1e20"]:
        bad.append(f"K_3 window, N=1e20: third-order left end is off by {gap:.2e}, stated 2e-5")

    # ---- fig_sticky, the sticky HDP prior (no longer included in Paper C)
    mc = {row["omega"]: row["P"] for row in D["sticky"]["monte_carlo"]}
    for om, q in PAPER["mc"].items():
        cmp(f"HDP Monte Carlo, omega={om:g}", mc[om], q)
    cmp("HDP Monte Carlo, omega=1 (text)", mc[1], PAPER["mc_text"]["P_1"])
    cmp("HDP, 1 - P at omega=1 (text)", 1 - mc[1], PAPER["mc_text"]["one_minus_P_1"])
    qd = {row["omega"]: row["P"] for row in D["sticky"]["quadrature"]}
    for om, q in PAPER["quad_omegaP"].items():
        cmp(f"HDP quadrature, omega P at omega={om}", om * qd[om], q)
    cmp("3 sqrt 3/(8 pi)", HDP_LIMIT, PAPER["hdp_limit"])
    cmp("HDP next term, omega (omega P/limit - 1) at 30000", 30000 * (30000 * qd[30000] / HDP_LIMIT - 1),
        PAPER["hdp_next_term"])

    # ---- Figure 6: the planar walk
    rows = D["planar"][(0.1, 1.0)]
    for row, qT, qg, qc in zip(rows, PAPER["planar_sT"], PAPER["planar_gap"], PAPER["planar_curve"]):
        L = log(row["N"])
        cmp(f"planar (0.1,1), N={row['N']}, sT*", 1.0 * row["T"], qT)
        cmp(f"planar (0.1,1), N={row['N']}, sT* - N(1-p_N)", row["T"] - row["nq"], qg)
        cmp(f"planar, N={row['N']}, -log 2 + log 2/(2L)", -LOG2 + LOG2 / (2 * L), qc)
    for pair, qs in PAPER["planar_T"].items():
        for row, q in zip(D["planar"][pair], qs):
            cmp(f"planar {pair}, N={row['N']}, T*", row["T"], q)
    for pair, qs in PAPER["planar_share"].items():
        for row, q in zip(D["planar"][pair], qs):
            q, fac = (q, 1) if isinstance(q, str) else q
            cmp(f"planar {pair}, N={row['N']}, 2S_N(u*)", row["S2"], q, factor=fac)
            if abs(row["S2"] - row["zero_turn"]) > 1e-9:
                bad.append(f"planar {pair}, N={row['N']}: 2S_N(u*) = {row['S2']} but the zero-turn part "
                           f"of the three-level sum is {row['zero_turn']}")
            if row["tail"] > 1e-15:
                bad.append(f"planar {pair}, N={row['N']}: truncation tail {row['tail']:.1e} is not negligible")
    cmp("switch limit 2 sqrt 2/(sqrt 2 + sqrt 5)", 2 * sqrt(2) / (sqrt(2) + sqrt(5)), PAPER["switch_limit"])

    if bad:
        raise SystemExit("disagreements with the paper:\n  " + "\n  ".join(bad))
    print("check: every quoted value agrees with the exact computation")


def arc_components(F, d):
    """The cyclic runs (arcs) of the face F of the d-cycle."""
    S = set(F)
    comps = []
    for i in F:
        if (i - 1) % d not in S:
            run = [i]
            while (run[-1] + 1) % d in S and len(run) < d:
                run.append((run[-1] + 1) % d)
            comps.append(run)
    return comps


def K_arc(k, d):
    """K_arc(k) from the research notes (uniform start on C_d)."""
    th = pi / (k + 1)
    return 2 / (d * (k + 1)) * (1 + cos(th)) ** 2 / np.sin(th) ** 3 * ((k + 1) / (2 * pi)) ** ((k - 1) / 2)


def b_k(k):
    return 0.5 * log(arc_lambda(k - 1) - arc_lambda(k)) - log(K_arc(k, 6) / K_arc(k - 1, 6))


# ================================================================ figure 1

TYPE_NAME = {"arc1": "1", "arc2": "2", "arc3": "3", "full5": "5"}


def fig_cycles(D):
    fig, (a, b) = plt.subplots(1, 2, figsize=(FULL, 2.45), gridspec_kw={"width_ratios": [1, 1.25]})

    # (a) the 6-cycle
    faces = all_faces(cycle_rates(6))
    pts = sorted({(round(lam, 12), len(F) - 1) for F, lam, c in faces if c}, key=lambda p: p[1])
    verts, taus = lower_left_hull(pts)
    hx, hy = zip(*verts)
    a.plot(hx, hy, "-", color="0.35", lw=0.9, zorder=1)
    win = {y for _, y in verts}
    for lam, y in pts:
        a.plot(lam, y, "o", ms=4.2, mec="k", mew=0.8, mfc="k" if y in win else "white", zorder=3)
        name = r"$C_6$" if y == 5 else ("1 state" if y == 0 else f"{y + 1} states")
        if y == 0:
            a.annotate(name, (lam, y), xytext=(0, -6), textcoords="offset points", ha="center", va="top")
        else:
            a.annotate(name, (lam, y), xytext=(6, 0), textcoords="offset points", ha="left", va="center")
    labels = ["$1$", r"$1+\sqrt{2}$", "$4.906$", r"$3+\sqrt{5}$"]
    offs = [(-5, -8), (-6, -8), (-7, -6), (-7, -4)]
    for (l0, y0), (l1, y1), lab, off in zip(verts, verts[1:], labels, offs):
        a.annotate(lab, ((l0 + l1) / 2, (y0 + y1) / 2), xytext=off, textcoords="offset points",
                   ha="right", va="top", color="0.2")
    a.plot([], [], "o", ms=4.2, mfc="k", mec="k", label="winner")
    a.plot([], [], "o", ms=4.2, mfc="white", mec="k", label="never wins")
    a.legend(frameon=False, loc="upper right", handletextpad=0.2, borderaxespad=0.2)
    a.set_xlim(-0.35, 2.3)
    a.set_ylim(-1.0, 5.6)
    a.set_yticks(range(6))
    a.set_xlabel(r"exit rate $\lambda_F$")
    a.set_ylabel(r"$|F|-1$")
    panel(a, "a", x=0.03, y=0.97)

    # (b) the 5-cycle
    cols = shades(4)
    Tmax = 16.0
    first = [1.0, 1 + sqrt(2), 2 + sqrt(2)]          # the switch values tau_i of C_5
    rows = [(40, 1.0), (72, 0.0)]
    for N, y in rows:
        C = D["cycles"][N]
        edges = [0.0] + [0.5 * (t["lo"] + t["hi"]) for t in C["transitions"]] + [Tmax]
        order = [C["transitions"][0]["before"]] + [t["after"] for t in C["transitions"]]
        # every grid point lies in the segment of its own type
        for T, ty in zip(C["grid"], C["types"]):
            if T <= Tmax:
                i = np.searchsorted(edges, T) - 1
                assert order[i] == ty, (N, T, ty)
        for i, ty in enumerate(order):
            c = cols[PAPER["C5_order"].index(ty)]
            b.broken_barh([(edges[i], edges[i + 1] - edges[i])], (y - 0.22, 0.44), facecolors=c,
                          edgecolors="k", linewidth=0.5)
            dark = PAPER["C5_order"].index(ty) >= 2
            b.text(0.5 * (edges[i] + edges[i + 1]), y, TYPE_NAME[ty], ha="center", va="center",
                   color="white" if dark else "k")
        L = log(N)
        b.plot([tk * L for tk in first], [y + 0.33] * 3, "v", ms=4.2, mfc="white", mec="k", mew=0.8, zorder=3)
    b.plot([], [], "v", ms=4.2, mfc="white", mec="k", mew=0.8, label=r"first order $\tau_i\log N$")
    b.legend(frameon=False, loc="upper right", handletextpad=0.2, borderaxespad=0.2)
    b.set_yticks([1.0, 0.0])
    b.set_yticklabels([r"$N=40$", r"$N=72$"])
    b.tick_params(axis="y", length=0)
    b.set_ylim(-0.55, 1.95)
    b.set_xlim(0, Tmax)
    b.set_xlabel(r"$T$")
    panel(b, "b")
    fig.subplots_adjust(left=0.07, right=0.99, wspace=0.28)
    save(fig, "fig_cycles")


# ================================================================ figure 2

def fig_window(D):
    t_ve, t_ef = window_limits()
    fig, (a, b) = plt.subplots(1, 2, figsize=(FULL, 2.4))

    # (a) the lines
    t = np.linspace(-0.6, -0.3, 400)
    lines = k3_lines(t)
    cols = shades(4, hi=0.75)
    spec = [((0,), r"$\ell_{\{1\}}=\ell_{\{2\}}$", "-", cols[0]),
            ((0, 1), r"$\ell_{\{1,2\}}$", "--", cols[1]),
            ((0, 2), r"$\ell_{\{1,3\}}=\ell_{\{2,3\}}$", "-.", cols[2]),
            ((0, 1, 2), r"$\ell_{[3]}$", ":", cols[3])]
    for F, lab, ls, c in spec:
        a.plot(t, lines[F], ls, color=c, lw=1.1, label=lab)
    assert np.allclose(lines[(0,)], lines[(1,)]) and np.allclose(lines[(0, 2)], lines[(1, 2)])
    env = np.max(np.array(list(lines.values())), axis=0)
    a.plot(t, env, "-", color="k", lw=2.4, alpha=0.3, solid_capstyle="butt", zorder=0)
    a.axvspan(t_ve, t_ef, color="0.85", lw=0, zorder=-1)
    a.set_xlim(-0.6, -0.3)
    a.set_ylim(-0.72, 0.6)
    a.set_xlabel(r"$t$")
    a.set_ylabel(r"$\ell_F(t)$")
    a.legend(frameon=False, loc="lower left", handlelength=2.2, borderaxespad=0.2)
    panel(a, "a", x=0.89)

    # (b) the ends at finite N
    rows = sorted(D["window"], key=lambda r: -r["L"])          # increasing (log L)/L
    x = np.array([log(r["L"]) / r["L"] for r in rows])
    ve = np.array([r["t_ve"] for r in rows])
    ef = np.array([r["t_ef"] for r in rows])
    b.fill_between(np.r_[0.0, x], np.r_[t_ve, ve], np.r_[t_ef, ef], color="0.9", lw=0, zorder=0)
    Ls = np.geomspace(rows[-1]["L"] * 0.97, 1e6, 400)
    b.plot(np.log(Ls) / Ls, [third_order_tve(L) for L in Ls], ":", color="0.35", lw=1.0,
           label=r"third order, $t_{ve}$")
    c2 = shades(2)
    b.plot(x, ve, "o", ms=3.6, color=c2[1], label=r"$t_{ve}$")
    b.plot(x, ef, "s", ms=3.4, mfc="white", mec=c2[1], mew=0.9, label=r"$t_{ef}$")
    b.plot([0, 0], [t_ve, t_ef], "*", ms=6, color="k", clip_on=False, zorder=4, label="limits")
    for r, xx in zip(rows, x):
        if r["N"] in ("1e6", "1e20"):
            e = int(r["N"][2:])
            b.annotate(rf"$N=10^{{{e}}}$", (xx, r["t_ef"]), xytext=(-5, 3), textcoords="offset points",
                       ha="right", va="bottom")
    b.set_xlim(0, 0.205)
    b.set_ylim(-0.475, -0.355)
    b.set_xlabel(r"$(\log L)/L$")
    b.set_ylabel(r"$t$")
    h, lab = b.get_legend_handles_labels()
    order = [1, 2, 0, 3]
    b.legend([h[i] for i in order], [lab[i] for i in order], frameon=False, loc="lower right",
             handlelength=1.8, borderaxespad=0.2)
    panel(b, "b")
    fig.subplots_adjust(left=0.08, right=0.99, wspace=0.3)
    save(fig, "fig_window")


# ================================================================ figure 3

def fig_sticky(D):
    mc = D["sticky"]["monte_carlo"]
    qd = D["sticky"]["quadrature"]
    fig, ax = plt.subplots(figsize=(COL, 2.55))
    om = np.geomspace(3e-3, 1e5, 300)
    ax.plot(om, HDP_LIMIT / om, "--", color="0.35", lw=0.9, label=r"$3\sqrt{3}/(8\pi\omega)$")
    ax.plot(om[om < 3], np.full((om < 3).sum(), 0.25), ":", color="0.35", lw=1.1, label=r"$1/4$")
    cols = shades(3)
    ax.errorbar([r["omega"] for r in mc], [r["P"] for r in mc], yerr=[r["se"] for r in mc], fmt="o", ms=3.8,
                mfc="white", mec=cols[1], ecolor=cols[1], mew=0.9, elinewidth=0.7, capsize=0,
                label=r"Monte Carlo, $10^6$ draws")
    ax.plot([r["omega"] for r in qd], [r["P"] for r in qd], "s", ms=3.2, color=cols[2], label="quadrature")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlim(3e-3, 1e5)
    ax.set_ylim(3e-6, 0.6)
    ax.set_xlabel(r"concentration $\omega$")
    ax.set_ylabel(r"$\mathbb{P}_\omega(D)$")
    h, lab = ax.get_legend_handles_labels()
    order = [3, 2, 0, 1]
    ax.legend([h[i] for i in order], [lab[i] for i in order], frameon=False, loc="lower left",
              handlelength=2.0, borderaxespad=0.3)
    save(fig, "fig_sticky")


# ================================================================ figure 4

def fig_planar(D):
    fig, (a, b) = plt.subplots(1, 2, figsize=(FULL, 2.45))
    Nticks = [40, 160, 640, 2560, 10240]

    # (a) reversals dominate
    rows = D["planar"][(0.1, 1.0)]
    Ns = np.array([r["N"] for r in rows])
    gap = np.array([1.0 * r["T"] - r["nq"] for r in rows])
    NN = np.geomspace(32, 13000, 300)
    a.axhline(-LOG2, color="0.35", ls=":", lw=1.1, label=r"$-\log2$")
    a.plot(NN, -LOG2 + LOG2 / (2 * np.log(NN)), "--", color="0.35", lw=0.9, label=r"$-\log2+\log2/(2L)$")
    a.plot(Ns, gap, "o-", color="k", ms=3.6, lw=0.8, label=r"exact, $(r,s)=(0.1,1)$")
    a.set_xscale("log")
    a.set_xlim(32, 13000)
    a.set_xticks(Nticks)
    a.set_xticklabels([str(n) for n in Nticks])
    a.minorticks_off()
    a.set_ylim(-0.705, -0.555)
    a.set_xlabel(r"$N$")
    a.set_ylabel(r"$sT^*_N-N(1-p_N)$")
    a.legend(frameon=False, loc="upper right", handlelength=2.2, borderaxespad=0.2)
    panel(a, "a", x=0.9, y=0.25)

    # (b) the zero-turn share
    pairs = [(0.1, 1.0), (0.3, 1.0), (0.5, 1.0), (1.0, 1.0), (1.0, 0.0)]
    limits = {(0.1, 1.0): 1.0, (0.3, 1.0): 1.0, (0.5, 1.0): 2 * sqrt(2) / (sqrt(2) + sqrt(5)),
              (1.0, 1.0): 0.0, (1.0, 0.0): 0.0}
    cols = shades(5)
    styles = ["-", "--", "-", "--", "-"]
    marks = ["o", "s", "^", "D", "v"]
    for lim in sorted(set(limits.values())):
        b.axhline(lim, color="0.6", ls=":", lw=0.8, zorder=0)
    b.text(12500, limits[(0.5, 1.0)] + 0.012, r"$0.7749$", ha="right", va="bottom", color="0.3")
    for pair, c, ls, mk in zip(pairs, cols, styles, marks):
        rows = D["planar"][pair]
        lab = rf"$({pair[0]:g},{pair[1]:g})$"
        b.plot([r["N"] for r in rows], [r["S2"] for r in rows], ls, marker=mk, color=c, ms=3.4, lw=0.9,
               mfc="white" if mk in "sD" else c, mec=c, label=lab)
    b.set_xscale("log")
    b.set_xlim(32, 13000)
    b.set_xticks(Nticks)
    b.set_xticklabels([str(n) for n in Nticks])
    b.minorticks_off()
    b.set_ylim(-0.04, 1.06)
    b.set_xlabel(r"$N$")
    b.set_ylabel(r"zero-turn share $2S_N(u^*_N)$")
    b.legend(frameon=False, loc="center right", title=r"$(r,s)$", title_fontsize=8, handlelength=2.2,
             borderaxespad=0.2, bbox_to_anchor=(1.0, 0.43))
    panel(b, "b", y=0.68)
    fig.subplots_adjust(left=0.08, right=0.99, wspace=0.28)
    save(fig, "fig_planar")


# ================================================================ main

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--recompute", action="store_true")
    ap.add_argument("--only")
    args = ap.parse_args()
    if args.only:
        key = args.only
        if key.startswith("cycles"):
            N = int(key[6:])
            cache(key, lambda: compute_cycles(N), True)
        elif key == "window":
            cache("window", compute_window, True)
        elif key == "sticky":
            cache("sticky", compute_sticky, True)
        elif key.startswith("planar:"):
            r, s = (float(v) for v in key[7:].split(","))
            cache(planar_key(r, s), lambda: compute_planar(r, s), True)
        else:
            raise SystemExit(f"unknown key {key}")
        raise SystemExit(0)
    D = load_all(args.recompute)
    check(D)
    fig_cycles(D)
    fig_window(D)
    fig_sticky(D)
    fig_planar(D)
