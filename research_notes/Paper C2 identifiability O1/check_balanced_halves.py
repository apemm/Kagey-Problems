# check_balanced_halves.py
# Problem 131, Paper C2, question O1. Exact tests of the balance condition
# p1 == p2 for one side X of a cut, where (in the coordinates of Q)
#   p1(lam) = pi_X (Lam_X - Q_X)^{-1} a,   p2(lam) = u (Lam_X - Q_X)^{-1} 1,
# Q[X,Y] = a b^T, Q[Y,X] = c u^T, normalized by pi_X.a = u.1.
# By the gluing formula, a cut-transpose that is neither Q nor Q* keeps the
# stationary occupation law exactly when one side is balanced.
# Necessary conditions found by expansion: u = pi_X * a (entrywise) and
# (pi_i q_ij - pi_j q_ji)(a_i - a_j) = 0 on X. Here: (A) a two-valued exit
# vector with circulation on its three-state level set, which is NOT a
# memoryless block; (B) the same with the level set made a memoryless block.
# Also (C): a d = 3 example showing that the discrete counts at N = 2 do not
# determine Q up to reversal.
# Run: py -I check_balanced_halves.py
import random
import sympy as sp

R = sp.Rational
random.seed(7)


def half(piX, Fs, Fk, a):
    """Q_X from fluxes: q_ij = (Fs_ij + Fk_ij)/pi_i, exit rate a_i (times b.1 = 1)."""
    n = len(piX)
    QX = sp.zeros(n, n)
    for i in range(n):
        for j in range(n):
            if i != j:
                QX[i, j] = (Fs[i][j] + Fk[i][j]) / piX[i]
        QX[i, i] = -sum(QX[i, j] for j in range(n) if j != i) - a[i]
    return QX


def p_diff(piX, QX, a, trials=3):
    n = len(piX)
    u = sp.Matrix([[piX[i] * a[i] for i in range(n)]])
    out = []
    for _ in range(trials):
        lam = [R(random.randint(1, 40), random.randint(1, 7)) for _ in range(n)]
        M = (sp.diag(*lam) - QX).inv()
        p1 = (sp.Matrix([piX]) * M * sp.Matrix(a))[0]
        p2 = (u * M * sp.ones(n, 1))[0]
        out.append(sp.nsimplify(p1 - p2))
    return out


piX = [R(1, 10), R(2, 10), R(3, 10), R(4, 10)]
k = R(1, 20)
Fk = [[0, k, -k, 0], [-k, 0, k, 0], [k, -k, 0, 0], [0, 0, 0, 0]]   # circulation on {1,2,3}

# (A) generic symmetric fluxes, a two-valued
Fs = [[0, R(1, 5), R(1, 4), R(1, 7)], [R(1, 5), 0, R(1, 3), R(1, 9)],
      [R(1, 4), R(1, 3), 0, R(1, 6)], [R(1, 7), R(1, 9), R(1, 6), 0]]
a = [1, 1, 1, 2]
QX = half(piX, Fs, Fk, a)
print("(A) level set {1,2,3} not memoryless: p1 - p2 at random lam =", p_diff(piX, QX, a))

# (B) make {1,2,3} a memoryless block: q_i4 equal for i in {1,2,3}
#     (Fs_i4 = t pi_i) and entry 4 -> i proportional to pi_i (Fs_4i = t pi_i again)
t = R(1, 2)
FsB = [[0, R(1, 5), R(1, 4), t * piX[0]], [R(1, 5), 0, R(1, 3), t * piX[1]],
       [R(1, 4), R(1, 3), 0, t * piX[2]], [t * piX[0], t * piX[1], t * piX[2], 0]]
QXB = half(piX, FsB, Fk, a)
print("(B) level set {1,2,3} memoryless:     p1 - p2 at random lam =", p_diff(piX, QXB, a))

# (C) d = 3, pi uniform, P = I + h(S + kC), C the cyclic circulation: every k gives
#     the same law of the counts at N = 2, for every h
h, kk = sp.symbols("h k")
z = sp.symbols("z1:4")
Ssym = sp.Matrix([[-2, 1, 1], [1, -2, 1], [1, 1, -2]])
Cyc = sp.Matrix([[0, 1, -1], [-1, 0, 1], [1, -1, 0]])
P = sp.eye(3) + h * (Ssym + kk * Cyc)
pi = sp.Matrix([[R(1, 3)] * 3])
Z = sp.diag(*z)
g2 = sp.expand((pi * Z * P * Z * sp.ones(3, 1))[0])
g3 = sp.expand((pi * Z * P * Z * P * Z * sp.ones(3, 1))[0])
print("(C) N = 2 count law depends on k:", sp.diff(g2, kk) != 0,
      "; N = 3 count law depends on k:", sp.expand(sp.diff(g3, kk)) != 0)
