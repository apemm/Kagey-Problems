# Section 8: the pair-face case of Lemma 1' against the draft's representation S_(b,a)(u) = (1-u)^a E[B_a(v X)]
import sympy as sp
u = sp.Symbol('u', positive=True)
def lemma1p(b, a):
    return sp.expand(sum(sp.binomial(a-1,K-1)*sum(sp.binomial(2,r)*sp.binomial(b-1,K-r)*u**(2*K-r) for r in range(3) if K-r>=0) for K in range(1, a+1)))
def draft(b, a):
    v = u/(1-u)
    tot = 0
    for j in range(b):                       # J ~ Bin(b-1, u), X | J ~ Gamma(J+2)
        pj = sp.binomial(b-1,j)*u**j*(1-u)**(b-1-j)
        EB = sum(sp.binomial(a-1,m-1)*v**m/sp.factorial(m)*sp.gamma(j+2+m)/sp.gamma(j+2) for m in range(1,a+1))
        tot += pj*EB
    return sp.simplify((1-u)**a*tot)
for b, a in [(3,1),(4,2),(5,3),(6,2)]:
    L = lemma1p(b,a); D = sp.expand(sp.simplify(draft(b,a)))
    print(b, a, "Lemma 1' main+end terms:", L, "| draft:", D, "| equal:", sp.simplify(L-D)==0)
