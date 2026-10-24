# Audit of Lemma 1 (continuum, (2.1)) and Lemma 1' (discrete) of 08_T2_boundary_layer.md
import itertools, sympy as sp
from fractions import Fraction as Fr
import random

def words(states, maxlen):
    for L in range(1, maxlen+1):
        for w in itertools.product(states, repeat=L):
            if all(w[k]!=w[k+1] for k in range(L-1)):
                yield w

def check_continuum(d, D):
    # states 0..d-1, i = d-1, G = 0..d-2; symbolic rates and start
    st = list(range(d)); i = d-1; G = st[:-1]
    q = {(a,b): sp.Symbol(f"q{a}{b}", positive=True) for a in st for b in st if a!=b}
    mu = [sp.Symbol(f"mu{a}", positive=True) for a in st]
    t = [sp.Symbol(f"t{a}") for a in st]   # t_i = x
    z = sp.Symbol("z")
    # LHS: H_F(t) truncated at total degree D in t
    H = 0
    for w in words(st, D + d):
        m = [w.count(a) for a in st]
        if min(m) == 0: continue
        if sum(mm-1 for mm in m) > D: continue
        wt = mu[w[0]]
        for k in range(len(w)-1): wt *= q[(w[k], w[k+1])]
        term = wt
        for a in st: term *= t[a]**(m[a]-1)/sp.factorial(m[a]-1)
        H += term
    # RHS: sum_K x^{K-1}/(K-1)! [z^K] ( e^{z sum c^-_j c^+_j s_j} sum_m W_z(m) prod s^{m-1}/(m-1)! )
    A = lambda a,b: q[(a,b)] + z*q[(a,i)]*q[(i,b)]
    pi = lambda a: mu[a] + z*mu[i]*q[(i,a)]
    e = lambda a: 1 + z*q[(a,i)]
    Phi0 = 0
    for w in words(G, D + d):
        m = [w.count(a) for a in G]
        if min(m) == 0: continue
        if sum(mm-1 for mm in m) > D: continue
        wt = pi(w[0]) * e(w[-1])
        for k in range(len(w)-1): wt *= A(w[k], w[k+1])
        term = wt
        for a in G: term *= t[a]**(m[a]-1)/sp.factorial(m[a]-1)
        Phi0 += term
    expo = sum(z*q[(a,i)]*q[(i,a)]*t[a] for a in G)
    E = sp.series(sp.exp(expo), z, 0, D+3).removeO()
    PhiZ = sp.expand(E*Phi0)
    RHS = 0
    for K in range(1, D+3):
        RHS += t[i]**(K-1)/sp.factorial(K-1) * PhiZ.coeff(z, K)
    # truncate both to total degree <= D in t
    def trunc(expr):
        P = sp.Poly(sp.expand(expr), *t)
        return sum(c*sp.prod([tt**e for tt,e in zip(t,mon)]) for mon,c in P.terms() if sum(mon)<=D)
    diff = sp.expand(trunc(H) - trunc(RHS))
    return diff

for d, D in [(3,4),(4,2)]:
    diff = check_continuum(d, D)
    print(f"Lemma 1 (2.1), d={d}, symbolic rates, total degree <= {D}: difference =", diff)

# Lemma 1' discrete, exact rationals
def check_discrete(d, N, seed):
    random.seed(seed)
    st = list(range(d)); i = d-1; G = st[:-1]
    Q = [[Fr(0)]*d for _ in st]
    for a in st:
        for b in st:
            if a!=b: Q[a][b] = Fr(random.randint(1,5), random.randint(1,4))
        Q[a][a] = -sum(Q[a][b] for b in st if b!=a)
    h = Fr(1, 40)
    mu = [Fr(random.randint(1,5)) for _ in st]; s = sum(mu); mu = [m/s for m in mu]
    P = [[(1 if a==b else 0) + h*Q[a][b] for b in st] for a in st]
    # brute-force law
    law = {}
    for path in itertools.product(st, repeat=N):
        p = mu[path[0]]
        for k in range(N-1): p *= P[path[k]][path[k+1]]
        n = tuple(path.count(a) for a in st)
        law[n] = law.get(n, 0) + p
    z = sp.Symbol("z")
    qi = -Q[i][i]
    bad = 0; tested = 0
    for n, val in law.items():
        if min(n) == 0: continue
        ni = n[i]; Np = N - ni; nhat = n[:-1]
        # P^{(z)}_{N'}(nhat)
        Mz = [[sp.Rational(P[a][b].numerator, P[a][b].denominator) + z*sp.Rational((h*h*Q[a][i]*Q[i][b]).numerator,(h*h*Q[a][i]*Q[i][b]).denominator) for b in G] for a in G]
        tot = 0
        for path in itertools.product(G, repeat=Np):
            if tuple(path.count(a) for a in G) != nhat: continue
            a0 = path[0]; aL = path[-1]
            term = (sp.Rational(mu[a0].numerator, mu[a0].denominator) + z*sp.Rational((h*mu[i]*Q[i][a0]).numerator,(h*mu[i]*Q[i][a0]).denominator))
            for k in range(Np-1): term *= Mz[path[k]][path[k+1]]
            term *= (1 + z*sp.Rational((h*Q[aL][i]).numerator,(h*Q[aL][i]).denominator))
            tot += term
        tot = sp.expand(tot)
        pred = 0
        for K in range(1, ni+1):
            pred += sp.binomial(ni-1, K-1) * sp.Rational(((1-h*qi)**(ni-K)).numerator, ((1-h*qi)**(ni-K)).denominator) * tot.coeff(z, K)
        tested += 1
        if sp.nsimplify(pred) != sp.Rational(val.numerator, val.denominator): bad += 1
    return tested, bad

for d, N, seed in [(3,6,1),(3,7,2),(4,6,3)]:
    tested, bad = check_discrete(d, N, seed)
    print(f"Lemma 1' discrete, d={d}, N={N}, exact rationals: compositions tested {tested}, mismatches {bad}")
