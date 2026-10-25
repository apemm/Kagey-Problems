# check_gluing_and_counterexample.py
# Problem 131, Paper C2, question O1. Exact checks, in rational arithmetic:
#  (1) the gluing formula F_Q - F_{Q'} = (p1 - p2)(q1 - q2)/(1 - alpha beta)
#      for the cut-transpose Q' across a cut X|Y (d = 4 example of the paper);
#  (2) a d = 5 chain with a memoryless block X = {1,2,3}: reversing Q inside X
#      gives Q' != Q, Q* with the same principal minors and F_{Q'} = F_Q, so the
#      stationary occupation law agrees at every T (and the discrete counts at
#      every N);
#  (3) the second-moment data DQ^m + (DQ^m)^T, m = 1, 2, on both examples.
# Run: py -I check_gluing_and_counterexample.py
import itertools
import sympy as sp

R = sp.Rational


def stationary(Q):
    n = Q.shape[0]
    A = Q.T.row_insert(n, sp.ones(1, n))
    b = sp.zeros(n, 1).row_insert(n, sp.Matrix([1]))
    return sp.Matrix(A.solve_least_squares(b)).T


def reversal(Q, pi):
    D = sp.diag(*pi)
    return D.inv() * Q.T * D


def minors(M):
    n = M.shape[0]
    return [M.extract(list(S), list(S)).det()
            for k in range(1, n + 1) for S in itertools.combinations(range(n), k)]


def F(Q, pi, lam):
    n = Q.shape[0]
    return sp.together((pi * (sp.diag(*lam) - Q).inv() * sp.ones(n, 1))[0])


def is_zero(expr):
    return sp.simplify(sp.together(expr)) == 0


def flip_Y(Q, pi, X, Y, a, b, c, u):
    """Generator point of the cut-transpose across X, with Q[X,Y] = a b^T and
    Q[Y,X] = c u^T. Factors are rescaled to pi_X.a = u.1 and b.1 = pi_Y.c, in
    which case Q'_X = Q_X, Q'_Y = Q*_Y, Q'[X,Y] = a c'^T with c' = D_Y c, and
    Q'[Y,X] = D_Y^{-1} b u^T, where D_Y = diag(pi_Y)."""
    piX = sp.Matrix([pi[i] for i in X]); piY = sp.Matrix([pi[j] for j in Y])
    t = (u.T * sp.ones(len(X), 1))[0] / (piX.T * a)[0]
    a = a * t; b = b / t
    s = (piY.T * c)[0] / (b.T * sp.ones(len(Y), 1))[0]
    b = b * s; c = c / s
    assert (piX.T * a)[0] == (u.T * sp.ones(len(X), 1))[0]
    assert (b.T * sp.ones(len(Y), 1))[0] == (piY.T * c)[0]
    DY = sp.diag(*piY)
    Qp = sp.zeros(*Q.shape)
    QX = Q.extract(X, X); QY = Q.extract(Y, Y)
    QYs = DY.inv() * QY.T * DY
    for ii, i in enumerate(X):
        for jj, j in enumerate(X):
            Qp[i, j] = QX[ii, jj]
        for jj, j in enumerate(Y):
            Qp[i, j] = a[ii] * pi[j] * c[jj]
    for ii, i in enumerate(Y):
        for jj, j in enumerate(Y):
            Qp[i, j] = QYs[ii, jj]
        for jj, j in enumerate(X):
            Qp[i, j] = b[ii] * u[jj] / pi[i]
    return Qp, (a, b, c, u)


def gluing_rhs(Q, pi, X, Y, a, b, c, u, lam):
    lX = [lam[i] for i in X]; lY = [lam[j] for j in Y]
    MX = (sp.diag(*lX) - Q.extract(X, X)).inv()
    MY = (sp.diag(*lY) - Q.extract(Y, Y)).inv()
    piX = sp.Matrix([[pi[i] for i in X]]); piY = sp.Matrix([[pi[j] for j in Y]])
    oX = sp.ones(len(X), 1); oY = sp.ones(len(Y), 1)
    p1 = (piX * MX * a)[0]; p2 = (u.T * MX * oX)[0]; al = (u.T * MX * a)[0]
    q1 = (b.T * MY * oY)[0]; q2 = (piY * MY * c)[0]; be = (b.T * MY * c)[0]
    return (p1 - p2) * (q1 - q2) / (1 - al * be), sp.factor(sp.together(p1 - p2)), \
        sp.factor(sp.together(q1 - q2))


def second_moment_data(Q, pi, m):
    D = sp.diag(*pi)
    M = D * Q ** m
    return M + M.T


# ---------------------------------------------------------------- (1)
print("=== (1) gluing formula on the d = 4 example of the paper")
Q4 = sp.Matrix([[R(-47, 10), R(7, 10), 1, 3], [R(13, 10), R(-93, 10), 2, 6],
                [2, 2, R(-22, 5), R(2, 5)], [1, 1, 2, -4]])
pi4 = stationary(Q4)
lam4 = sp.symbols("l1:5")
X, Y = [0, 1], [2, 3]
Q4p, fac = flip_Y(Q4, pi4, X, Y, sp.Matrix([1, 2]), sp.Matrix([1, 3]),
                  sp.Matrix([2, 1]), sp.Matrix([1, 1]))
print("Q' equals the paper's generator point (q'_13 = 50/21):", Q4p[0, 2] == R(50, 21),
      " q'_41 =", Q4p[3, 0], " q'_43 =", Q4p[3, 2])
rhs, dp, dq = gluing_rhs(Q4, pi4, X, Y, *fac, lam4)
lhs = F(Q4, pi4, lam4) - F(Q4p, pi4, lam4)
print("F_Q - F_Q' - (p1-p2)(q1-q2)/(1-alpha beta) == 0 :", is_zero(lhs - rhs))
print("p1 - p2 =", dp)
print("q1 - q2 =", dq)
for m in (1, 2):
    print("m =", m, " second-moment data differ:",
          second_moment_data(Q4, pi4, m) != second_moment_data(Q4p, pi4, m))

# ---------------------------------------------------------------- (2)
print("\n=== (2) memoryless block, d = 5, X = {1,2,3}, Y = {4,5}")
# X block: cyclic rates 2 one way, 1 the other way (doubly stochastic, not reversible)
# each x in X jumps to 4 at rate 1 and to 5 at rate 2 (same exit rate 3, same landing law)
# 4 jumps to each x at rate 1, 5 to each x at rate 2 (landing law uniform = pi_X/pi(X))
# 4 -> 5 at rate 1, 5 -> 4 at rate 4
Q5 = sp.Matrix([[0, 2, 1, 1, 2],
                [1, 0, 2, 1, 2],
                [2, 1, 0, 1, 2],
                [1, 1, 1, 0, 1],
                [2, 2, 2, 4, 0]])
for i in range(5):
    Q5[i, i] = -sum(Q5[i, j] for j in range(5) if j != i)
pi5 = stationary(Q5)
print("pi =", list(pi5))
Q5s = reversal(Q5, pi5)
X, Y = [0, 1, 2], [3, 4]
Q5p = Q5.copy()
QXs = reversal(Q5.extract(X, X), sp.Matrix([[pi5[i] for i in X]]))
for ii, i in enumerate(X):
    for jj, j in enumerate(X):
        Q5p[i, j] = QXs[ii, jj]
print("Q' (X block reversed):"); sp.pprint(Q5p)
print("Q' is a generator with stationary law pi:",
      Q5p * sp.ones(5, 1) == sp.zeros(5, 1) and pi5 * Q5p == sp.zeros(1, 5))
print("Q' != Q:", Q5p != Q5, "  Q' != Q*:", Q5p != Q5s, "  Q* != Q:", Q5s != Q5)
print("ranks of Q[X,Y], Q[Y,X]:", Q5.extract(X, Y).rank(), Q5.extract(Y, X).rank())
print("same 31 principal minors:", minors(-Q5) == minors(-Q5p))
lam5 = sp.symbols("l1:6")
F5, F5p, F5s = F(Q5, pi5, lam5), F(Q5p, pi5, lam5), F(Q5s, pi5, lam5)
print("F_Q - F_Q' == 0 :", is_zero(F5 - F5p))
print("F_Q - F_Q* == 0 :", is_zero(F5 - F5s))
# the same Q' is flip of the X half; check it against the gluing formula
Q5f, fac5 = flip_Y(Q5, pi5, Y, X, sp.Matrix([3, 6]),
                   sp.Matrix([R(1, 3)] * 3), sp.ones(3, 1), sp.Matrix([1, 2]))
print("generator point of the cut-transpose across Y (flips X) equals Q':", Q5f == Q5p)
rhs5, dp5, dq5 = gluing_rhs(Q5, pi5, Y, X, *fac5, lam5)
print("gluing: p - p for the Y half =", dp5, "; for the X half =", dq5)
for m in (1, 2, 3):
    print("m =", m, " second-moment data equal:",
          second_moment_data(Q5, pi5, m) == second_moment_data(Q5p, pi5, m))
# discrete counts, P = I + h Q, every N up to 6, at h = 1/20
h = R(1, 20)
z = sp.symbols("z1:6")
Z = sp.diag(*z)
P, Pp = sp.eye(5) + h * Q5, sp.eye(5) + h * Q5p
ok = True
v, vp = pi5 * Z, pi5 * Z
for N in range(1, 7):
    g = sp.expand((v * sp.ones(5, 1))[0]); gp = sp.expand((vp * sp.ones(5, 1))[0])
    ok = ok and sp.expand(g - gp) == 0
    v, vp = v * P * Z, vp * Pp * Z
print("discrete count laws equal for N = 1..6 (h = 1/20):", ok)

# ---------------------------------------------------------------- (2b)
print("\n=== (2b) the X half of the d = 5 example is balanced (p1 = p2), the Y half is not")
print("p1 - p2 for the X half (should be 0):", dq5)
print("q1 - q2 for the Y half (nonzero):", dp5)
