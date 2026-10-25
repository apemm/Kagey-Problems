# repro_cut_example.py
# Problem 131, Paper C2, question O1. Exact check of the d = 4 cut example of
# sec_minors.tex: the cut-transpose generator point Q', the time reversal Q*,
# the stationary resolvent F(lam) = pi (diag(lam) - Q)^{-1} 1, and the first
# moment pi (Q - W)^n 1 that separates Q' from Q.
# Run: py -I repro_cut_example.py
import sympy as sp

R = sp.Rational
Q = sp.Matrix([[R(-47, 10), R(7, 10), 1, 3],
               [R(13, 10), R(-93, 10), 2, 6],
               [2, 2, R(-22, 5), R(2, 5)],
               [1, 1, 2, -4]])
d = 4
X, Y = [0, 1], [2, 3]


def stationary(Q):
    n = Q.shape[0]
    A = Q.T.copy()
    A = A.row_insert(n, sp.ones(1, n))
    b = sp.zeros(n, 1).row_insert(n, sp.Matrix([1]))
    sol = A.solve_least_squares(b)
    return sp.Matrix(sol).T


def reversal(Q, pi):
    D = sp.diag(*pi)
    return D.inv() * Q.T * D


def principal_minors(M):
    import itertools
    n = M.shape[0]
    out = {}
    for k in range(1, n + 1):
        for S in itertools.combinations(range(n), k):
            out[S] = sp.simplify(M.extract(list(S), list(S)).det())
    return out


pi = stationary(Q)
Qs = reversal(Q, pi)
# cut-transpose of C = -Q across X with C[X,Y] = -a b^T, C[Y,X] = -c u^T
a = sp.Matrix([1, 2]); b = sp.Matrix([1, 3])
c = sp.Matrix([2, 1]); u = sp.Matrix([1, 1])
C = -Q
assert C.extract(X, Y) == -a * b.T and C.extract(Y, X) == -c * u.T
Cp = sp.zeros(4, 4)
Cp[0:2, 0:2] = C.extract(X, X)
Cp[0:2, 2:4] = -a * c.T
Cp[2:4, 0:2] = -b * u.T
Cp[2:4, 2:4] = C.extract(Y, Y).T
piY = sp.Matrix([pi[2], pi[3]])
s0 = (b.T * sp.ones(2, 1))[0] / (c.T * piY)[0]
x = sp.Matrix([1, 1, s0 * pi[2], s0 * pi[3]])
assert sp.simplify(Cp * x) == sp.zeros(4, 1)
Dx = sp.diag(*x)
Qp = sp.simplify(-Dx.inv() * Cp * Dx)
pip = stationary(Qp)
print("pi      =", list(pi))
print("pi(Q')  =", list(pip), " equal:", sp.simplify(pi - pip) == sp.zeros(1, 4))
print("Q' =")
sp.pprint(Qp)
print("q'_13, q'_41, q'_43 =", Qp[0, 2], Qp[3, 0], Qp[3, 2])
print("Q' == Q*:", sp.simplify(Qp - Qs) == sp.zeros(4, 4), "  q*_12 =", Qs[0, 1])
m1, m2 = principal_minors(-Q), principal_minors(-Qp)
print("same 15 principal minors:", all(sp.simplify(m1[k] - m2[k]) == 0 for k in m1))

lam = sp.symbols("l1:5")
w = sp.symbols("w1:5")


def F(Q, pi):
    M = sp.diag(*lam) - Q
    return sp.together((pi * M.inv() * sp.ones(4, 1))[0])


FQ, FQs, FQp = F(Q, pi), F(Qs, pi), F(Qp, pi)
print("F_Q - F_Q* == 0 :", sp.simplify(FQ - FQs) == 0)
diff = sp.factor(sp.simplify(FQ - FQp))
print("F_Q - F_Q' =", diff)

W = sp.diag(*w)
one = sp.ones(4, 1)
P = sp.eye(4); Pp = sp.eye(4)
for n in range(1, 7):
    P = P * (Q - W); Pp = Pp * (Qp - W)
    dn = sp.expand((pi * P * one)[0] - (pi * Pp * one)[0])
    if dn != 0:
        print("first separating n =", n)
        print("difference =", sp.factor(dn))
        print("terms:", sp.Poly(dn, *w).terms())
        break
    else:
        print("n =", n, ": equal")
