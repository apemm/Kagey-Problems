"""Shared functions for the checks of Paper G: the exact law of the occupation count.

Setting. Alternating runs with mass functions f_+ and f_- on {1, 2, ...} and tails
T(n) = P(X >= n). The convolution powers u_m = f^{*m} are computed by direct convolution, so all
terms are nonnegative. For a fresh plus start the bivariate renewal arrays

    A(k, j) = sum_{m>=0} u+_m(k) u-_m(j),      B(k, j) = sum_{m>=1} u+_m(k) u-_{m-1}(j)

are the probabilities that a plus run, respectively a minus run, starts after exactly k plus steps
and j minus steps. Splitting on the run in progress at step N gives, with j = N - k,

    F+_N(k) = sum_{k'<k} A(k', j) T+(k-k') + sum_{j'<j} B(k, j') T-(j-j').

This is the form used by eq:run-sum of the paper. The functions below compute it, the Lamperti
density, the number of sign changes of a sequence of first differences, and a brute-force sum over
all sign strings for small N. They are imported by the verify scripts and do nothing when run.
"""
import hashlib
import itertools
import platform
from datetime import date
from pathlib import Path

import numpy as np
from scipy.special import zeta

HERE = Path(__file__).resolve().parent


def zeta_law(a, nmax, shift=0):
    """f(n) proportional to (n + shift)^(-a-1) on n >= 1, and T(n) = P(X >= n), for n <= nmax + 1."""
    z = zeta(a + 1, 1 + shift)
    n = np.arange(nmax + 2, dtype=float)
    f = np.zeros(nmax + 2)
    f[1:] = (n[1:] + shift) ** (-a - 1) / z
    T = np.ones(nmax + 2)
    T[1:] = zeta(a + 1, n[1:] + shift) / z
    return f, T


def convolution_powers(f, nmax):
    """U[m, k] = f^{*m}(k) for 0 <= m, k <= nmax."""
    U = np.zeros((nmax + 1, nmax + 1))
    U[0, 0] = 1.0
    for m in range(1, nmax + 1):
        prev = U[m - 1, m - 1:]
        c = np.convolve(prev, f[1:nmax + 2 - m])
        U[m, m:] = c[:nmax + 1 - m]
    return U


def arrays(Up, Um):
    """The arrays A and B of a fresh plus start from the convolution powers of the two signs."""
    A = Up.T @ Um
    B = Up[1:].T @ Um[:-1]
    return A, B


def fresh_plus(A, B, Tp, Tm, N):
    """The law F+_N(k), 0 <= k <= N, of the number of plus steps for a fresh plus start."""
    P = np.zeros(N + 1)
    for k in range(N + 1):
        j = N - k
        s = 0.0
        if k >= 1:
            s += A[0:k, j] @ Tp[k:0:-1]
        if j >= 1:
            s += B[k, 0:j] @ Tm[j:0:-1]
        P[k] = s
    return P


def lamperti(x, a, b=1.0):
    """The density L_{a,b}(x) on (0, 1)."""
    c = np.cos(np.pi * a)
    return (np.sin(np.pi * a) / np.pi * b * x ** (a - 1) * (1 - x) ** (a - 1)
            / (b * b * x ** (2 * a) + 2 * b * c * x ** a * (1 - x) ** a + (1 - x) ** (2 * a)))


def sign_changes(P):
    """Number of sign changes of the first differences of P and the indices k where they occur.

    A change between the differences P(k) - P(k-1) and P(k+1) - P(k) is reported at k, so k is the
    position of a strict local extremum. Zero differences are skipped."""
    d = np.diff(P)
    idx = np.nonzero(d != 0)[0]
    s = np.sign(d[idx])
    ch = np.nonzero(s[1:] != s[:-1])[0]
    return len(ch), [int(idx[i + 1]) for i in ch]


def brute(N, fp, Tp, fm, Tm, nup=None, num=None, Qp=None, Qm=None):
    """P_N by a sum over all sign strings. Without nup, num the start is fresh plus. Otherwise the
    first run has sign + and length d with probability nup[d] (d < N), sign + and length >= N
    with probability Qp, and the same for the minus sign."""
    P = np.zeros(N + 1)
    f = {1: fp, 0: fm}
    T = {1: Tp, 0: Tm}
    for s in itertools.product((0, 1), repeat=N):
        if nup is None and s[0] == 0:
            continue
        runs = [(key, len(list(g))) for key, g in itertools.groupby(s)]
        sig0, r0 = runs[0]
        if len(runs) == 1:
            if nup is None:
                p = Tp[r0]
            else:
                p = Qp if sig0 == 1 else Qm
        else:
            if nup is None:
                p = fp[r0]
            else:
                p = nup[r0] if sig0 == 1 else num[r0]
            for key, r in runs[1:-1]:
                p *= f[key][r]
            key, r = runs[-1]
            p *= T[key][r]
        P[sum(s)] += p
    return P


def sha256_of(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class Report:
    """Collects lines and PASS/FAIL checks, and writes data/<name>_output.txt with a header."""

    def __init__(self, script):
        self.script = Path(script)
        self.lines = []
        self.fails = []

    def log(self, msg=""):
        print(msg, flush=True)
        self.lines.append(msg)

    def check(self, name, cond, detail=""):
        self.log(f"{'PASS' if cond else 'FAIL'}  {name}" + (f"  ({detail})" if detail else ""))
        if not cond:
            self.fails.append(name)

    def write(self, elapsed):
        name = self.script.stem
        self.log(f"\n{'PASS' if not self.fails else 'FAIL'}  {name} ({len(self.fails)} failures, {elapsed:.1f} s)")
        header = [f"# script: {self.script.name}",
                  f"# sha256: {sha256_of(self.script)}",
                  f"# uses lamperti_law.py sha256: {sha256_of(HERE / 'lamperti_law.py')}",
                  f"# date: {date.today().isoformat()}",
                  f"# python {platform.python_version()}, numpy {np.__version__}", ""]
        out = HERE / "data" / f"{name}_output.txt"
        out.parent.mkdir(exist_ok=True)
        out.write_text("\n".join(header + self.lines) + "\n", encoding="utf-8", newline="\n")
        return 0 if not self.fails else 1
