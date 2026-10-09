"""Checks for the rigidity section and for part (b) of the lumping theorem.

1. Reversing the inside of a module whose entrance law is stationary for the
   inside chain keeps the law of L(t), for any start that follows the entrance
   law inside the module. Tested with one outside state (d = 4, not a cut) and
   with two outside states (d = 5).
2. In every tie found so far, G and G' have the same principal minors, and so
   do G - 1 mu^T and G' - 1 mu^T.
3. For a tie between (mu, G) and (mu, reversal of G) the start need not be
   stationary (the d = 4 example of item 1), and for a random chain with a
   start that is not stationary the reversal is not a tie.
"""
import itertools
import numpy as np
from scipy.linalg import expm

rng = np.random.default_rng(7)


def gen(A):
    A = np.array(A, dtype=float)
    np.fill_diagonal(A, 0.0)
    return A - np.diag(A.sum(axis=1))


def stat(G):
    d = len(G)
    M = np.vstack([G.T, np.ones(d)])
    b = np.zeros(d + 1)
    b[-1] = 1.0
    return np.linalg.lstsq(M, b, rcond=None)[0]


def reverse(G, pi):
    return gen(G.T * pi[None, :] / pi[:, None])


def law_gap(mu, G, G2, trials=40):
    """Largest gap between the two Laplace transforms of L(t) over random points."""
    d = len(G)
    worst = 0.0
    for _ in range(trials):
        lam = rng.uniform(0.0, 3.0, d)
        t = rng.choice([0.3, 1.0, 4.0])
        a = mu @ expm(t * (G - np.diag(lam))) @ np.ones(d)
        b = mu @ expm(t * (G2 - np.diag(lam))) @ np.ones(d)
        worst = max(worst, abs(a - b))
    return worst


def minors_gap(A, B):
    d = len(A)
    worst = 0.0
    for k in range(1, d + 1):
        for U in itertools.combinations(range(d), k):
            U = list(U)
            worst = max(worst, abs(np.linalg.det(A[np.ix_(U, U)]) - np.linalg.det(B[np.ix_(U, U)])))
    return worst


def module_chain(m, n_out):
    """A chain with module M = first m states and n_out outside states.
    The entrance law nu is stationary for the inside chain."""
    d = m + n_out
    inside = gen(rng.uniform(0.2, 2.0, (m, m)))
    nu = stat(inside)
    A = np.zeros((d, d))
    A[:m, :m] = inside - np.diag(np.diag(inside))
    gamma = rng.uniform(0.2, 1.5, n_out)
    r = rng.uniform(0.2, 1.5, n_out)
    A[:m, m:] = gamma[None, :]
    A[m:, :m] = r[:, None] * nu[None, :]
    A[m:, m:] = rng.uniform(0.2, 2.0, (n_out, n_out))
    G = gen(A)
    A2 = A.copy()
    rev_in = reverse(inside, nu)
    A2[:m, :m] = rev_in - np.diag(np.diag(rev_in))
    G2 = gen(A2)
    return G, G2, nu


print("1. reverse the inside, keep the outside")
for m, n_out in ((3, 1), (3, 2), (4, 3)):
    G, G2, nu = module_chain(m, n_out)
    d = m + n_out
    out = rng.uniform(0.5, 1.5, n_out)
    a = 0.37
    mu = np.concatenate([a * nu, (1 - a) * out / out.sum()])
    pi = stat(G)
    print("   d = %d, outside states %d: max |G - G'| = %.3f, |mu - pi| = %.3f, law gap %.1e"
          % (d, n_out, abs(G - G2).max(), abs(mu - pi).max(), law_gap(mu, G, G2)))
    one_mu = np.outer(np.ones(d), mu)
    print("      principal minors: G vs G' %.1e, G - 1mu vs G' - 1mu %.1e"
          % (minors_gap(G, G2), minors_gap(G - one_mu, G2 - one_mu)))
    if n_out == 1:
        print("      G' is the reversal of G: %.1e" % abs(G2 - reverse(G, pi)).max())

print("3. a random chain, start not stationary: the reversal is not a tie")
for d in (3, 4, 5):
    G = gen(rng.uniform(0.2, 2.0, (d, d)))
    pi = stat(G)
    mu = rng.uniform(0.5, 1.5, d)
    mu /= mu.sum()
    Gh = reverse(G, pi)
    one_mu = np.outer(np.ones(d), mu)
    one_pi = np.outer(np.ones(d), pi)
    print("   d = %d: law gap from mu %.1e, from pi %.1e, minors of G - 1mu differ by %.1e, of G - 1pi by %.1e"
          % (d, law_gap(mu, G, Gh), law_gap(pi, G, Gh),
             minors_gap(G - one_mu, Gh - one_mu), minors_gap(G - one_pi, Gh - one_pi)))
