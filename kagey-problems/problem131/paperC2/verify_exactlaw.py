"""Exact checks of Section `sec:exactlaw` (the exact occupation law).

Everything is computed in rational arithmetic with sympy. For a generator Q with stationary law
pi, F_Q(lam) = pi (diag(lam) - Q)^(-1) 1 is the stationary Laplace transform of Lemma
`lem:reductions`, and Sigma_m = D Q^m + (D Q^m)^T with D = diag(pi).

  (1) The five-state example `ex:five-state`. The block B = {1,2,3} is memoryless (common exit
      rate 3 with landing law (1/3, 2/3), entries uniform on B), pi = (4,4,4,6,3)/21, and Q^[B]
      (Q with its B block replaced by the time reversal of that block) is a generator with
      stationary law pi, different from Q and from Q*. Both have the same 31 principal minors,
      F_Q - F_{Q^[B]} = 0 as a rational function, the same Sigma_1, Sigma_2 and Sigma_3, and the
      same law of the counts of I + hQ from pi for N = 1..6 at h = 1/20. The start e_1 separates
      them. Q^[B] is the time reversal of the generator point of the cut-transpose across B
      (Remark `rem:memoryless-cut`). The eigenvalues of K^2 are -7/8 and -3/4, each twice, and
      the symmetric part does not couple the two eigenplanes.
  (2) The four-state cut example after Corollary `thm:nonreversible`. The generator point Q' of
      the cut-transpose has the stationary law pi = (2226, 1134, 2675, 3638)/9673 of Q. The
      gluing formula of Proposition `prop:gluing` holds as an identity of rational functions,
      pi (Q - W)^n 1 agrees for n = 1, 2, and at n = 3 the difference is
      29 (w1 - w2)(w3 - w4)/9673.
  (3) Second moments for d <= 4 (Theorem `thm:second-moments`(i)). For several generators with
      3 and 4 states, every antisymmetric K' with K' 1 = 0 and K' D^(-1) K' = K D^(-1) K, where
      K is the antisymmetric part of D Q, is K or -K. So pi, Sigma_1 and Sigma_2 give Q or Q*.
  (4) The discrete second moments of Remark `rem:one-N`, E_pi[n n^T] = N^2 D +
      sum_{k=1}^{N-1} h^k C(N+1, k+2) Sigma_k, by exact enumeration for N = 2, 3, 4, and the fact
      that the law of the counts at N = 2 does not see a circulation while the law at N = 3 does.

Run:  py -I verify_exactlaw.py   (about 15 seconds)
"""

import itertools

import sympy as sp

R = sp.Rational
CHECKS = 0


def ok(cond, what):
    global CHECKS
    if not cond:
        raise AssertionError(what)
    CHECKS += 1
    print("  ok   ", what)


def generator(off):
    Q = sp.Matrix(off)
    for i in range(Q.shape[0]):
        Q[i, i] = 0
        Q[i, i] = -sum(Q[i, :])
    return Q


def stationary(Q):
    n = Q.shape[0]
    A = Q.T.col_join(sp.ones(1, n))
    b = sp.zeros(n, 1).col_join(sp.Matrix([1]))
    sol, params = A.gauss_jordan_solve(b)
    assert not params
    return sol.T


def reversal(Q, pi):
    D = sp.diag(*pi)
    return D.inv() * Q.T * D


def minors(M):
    n = M.shape[0]
    return [M.extract(list(S), list(S)).det()
            for k in range(1, n + 1) for S in itertools.combinations(range(n), k)]


def F(Q, start, lam):
    n = Q.shape[0]
    M = sp.diag(*lam) - Q
    return sp.cancel((start * M.adjugate() * sp.ones(n, 1))[0] / M.det())


def sigma(Q, pi, m):
    A = sp.diag(*pi) * Q ** m
    return A + A.T


def count_laws(P, start, z, Nmax):
    """Probability generating functions of the composition n(N), N = 1..Nmax."""
    n = P.shape[0]
    Z = sp.diag(*z)
    v = start * Z
    out = []
    for _ in range(Nmax):
        out.append(sp.expand((v * sp.ones(n, 1))[0]))
        v = sp.expand(v * P * Z)
    return out


# ------------------------------------------------------------------------------------------- (1)
print("(1) the five-state example with a memoryless block B = {1,2,3}")
Q5 = generator([[0, 2, 1, 1, 2],
                [1, 0, 2, 1, 2],
                [2, 1, 0, 1, 2],
                [1, 1, 1, 0, 1],
                [2, 2, 2, 4, 0]])
pi5 = stationary(Q5)
ok(list(pi5) == [R(4, 21)] * 3 + [R(6, 21), R(3, 21)], "pi = (4,4,4,6,3)/21")
B, Y = [0, 1, 2], [3, 4]
piB = sum(pi5[i] for i in B)
kappa = 3
nu = [R(1, 3), R(2, 3)]
c = [Q5[y, 0] * piB / pi5[0] for y in Y]
ok(all(Q5[i, Y[k]] == kappa * nu[k] for i in B for k in range(2)),
   "every state of B leaves B at rate 3 with landing law (1/3, 2/3)")
ok(all(Q5[Y[k], i] == c[k] * pi5[i] / piB for i in B for k in range(2)),
   "every jump into B lands with law pi_B/pi(B), with c = (3, 6)")
ok(c == [3, 6], "c = (3, 6)")
QB = Q5.extract(B, B)
QBs = reversal(QB, [pi5[i] for i in B])
Q5B = Q5.copy()
for a, i in enumerate(B):
    for b, j in enumerate(B):
        Q5B[i, j] = QBs[a, b]
ok(QBs == QB.T, "pi_B is uniform, so the reversed block is the transposed block")
ok(Q5B * sp.ones(5, 1) == sp.zeros(5, 1) and pi5 * Q5B == sp.zeros(1, 5),
   "Q^[B] is a generator with stationary law pi")
Q5s = reversal(Q5, pi5)
ok(Q5B != Q5 and Q5B != Q5s and Q5s != Q5, "Q^[B] differs from Q and from Q*, and Q is not reversible")
ok(minors(-Q5) == minors(-Q5B), "Q and Q^[B] have the same 31 principal minors")
lam5 = sp.symbols("l1:6")
ok(sp.cancel(F(Q5, pi5, lam5) - F(Q5B, pi5, lam5)) == 0, "F_Q - F_{Q^[B]} = 0 as a rational function")
e1 = sp.Matrix([[1, 0, 0, 0, 0]])
ok(sp.cancel(F(Q5, e1, lam5) - F(Q5B, e1, lam5)) != 0, "from the start e_1 the transforms differ")
for m in (1, 2, 3):
    ok(sigma(Q5, pi5, m) == sigma(Q5B, pi5, m), f"Sigma_{m} agrees")
z5 = sp.symbols("z1:6")
h = R(1, 20)
L1 = count_laws(sp.eye(5) + h * Q5, pi5, z5, 6)
L2 = count_laws(sp.eye(5) + h * Q5B, pi5, z5, 6)
ok(all(sp.expand(a - b) == 0 for a, b in zip(L1, L2)),
   "the laws of the counts of I + hQ and I + hQ^[B] from pi agree for N = 1..6, h = 1/20")
# Q^[B] is the time reversal of the generator point of the cut-transpose across X = B
X = B
a_vec = sp.ones(3, 1)
b_vec = sp.Matrix([kappa * x for x in nu])
u_vec = sp.Matrix([pi5[i] for i in X])
c_vec = sp.Matrix([cy / piB for cy in c])
ok(Q5.extract(X, Y) == a_vec * b_vec.T and Q5.extract(Y, X) == c_vec * u_vec.T,
   "factors a = 1, b = 3 nu, c = c/pi(B), u = pi_B of the cut B | {4,5}")
DY = sp.diag(*[pi5[y] for y in Y])
Qpp = sp.zeros(5, 5)
Qpp[0:3, 0:3] = QB
Qpp[0:3, 3:5] = a_vec * (DY * c_vec).T
Qpp[3:5, 0:3] = DY.inv() * b_vec * u_vec.T
Qpp[3:5, 3:5] = reversal(Q5.extract(Y, Y), [pi5[y] for y in Y])
ok(Qpp * sp.ones(5, 1) == sp.zeros(5, 1) and pi5 * Qpp == sp.zeros(1, 5),
   "the generator point Q'' of the cut-transpose across B has stationary law pi")
ok(reversal(Qpp, pi5) == Q5B, "Q^[B] is the time reversal of Q''")
# the spectral data of Theorem thm:second-moments(ii), in the rational similar form
D5 = sp.diag(*pi5)
A5 = D5 * Q5
K5 = (A5 - A5.T) / 2
S5 = (A5 + A5.T) / 2
Nr = D5.inv() * K5 * D5.inv() * K5          # similar to K^2 in symmetrized coordinates
Sr = D5.inv() * S5                          # similar to S, by the same similarity
t = sp.symbols("t")
ok(sp.expand(Nr.charpoly(t).as_expr() - t * (t + R(7, 8)) ** 2 * (t + R(3, 4)) ** 2) == 0,
   "K^2 has the eigenvalues -7/8 and -3/4, each twice, and 0 once")
eig = [R(-7, 8), R(-3, 4), 0]
proj = []
for k in range(2):
    P = sp.eye(5)
    for j in range(3):
        if j != k:
            P = P * (Nr - eig[j] * sp.eye(5)) / (eig[k] - eig[j])
    proj.append(P)
ok(proj[0] * Sr * proj[1] == sp.zeros(5, 5), "S does not couple the two eigenplanes of K^2")

# ------------------------------------------------------------------------------------------- (2)
print("(2) the four-state cut example")
Q4 = sp.Matrix([[R(-47, 10), R(7, 10), 1, 3], [R(13, 10), R(-93, 10), 2, 6],
                [2, 2, R(-22, 5), R(2, 5)], [1, 1, 2, -4]])
pi4 = stationary(Q4)
ok(list(pi4 * 9673) == [2226, 1134, 2675, 3638], "pi = (2226, 1134, 2675, 3638)/9673")
X, Y = [0, 1], [2, 3]
a, b = sp.Matrix([1, 2]), sp.Matrix([1, 3])
c, u = sp.Matrix([2, 1]), sp.Matrix([1, 1])
ok(Q4.extract(X, Y) == a * b.T and Q4.extract(Y, X) == c * u.T, "Q[X,Y] = a b^T and Q[Y,X] = c u^T")
piX = sp.Matrix([pi4[i] for i in X])
piY = sp.Matrix([pi4[j] for j in Y])
s = (u.T * sp.ones(2, 1))[0] / (piX.T * a)[0]
a, b = a * s, b / s                          # normalization pi_X . a = u . 1
ok((b.T * sp.ones(2, 1))[0] == (piY.T * c)[0], "then b . 1 = pi_Y . c")
DY = sp.diag(*piY)
Q4p = sp.zeros(4, 4)
Q4p[0:2, 0:2] = Q4.extract(X, X)
Q4p[0:2, 2:4] = a * (DY * c).T
Q4p[2:4, 0:2] = DY.inv() * b * u.T
Q4p[2:4, 2:4] = reversal(Q4.extract(Y, Y), list(piY))
ok(Q4p * sp.ones(4, 1) == sp.zeros(4, 1) and pi4 * Q4p == sp.zeros(1, 4),
   "the generator point Q' is a generator with stationary law pi")
ok((Q4p[0, 2], Q4p[3, 0], Q4p[3, 2]) == (R(50, 21), R(63, 34), R(5, 17)),
   "q'_13 = 50/21, q'_41 = 63/34, q'_43 = 5/17, as in the text")
ok(minors(-Q4) == minors(-Q4p), "Q' has the 15 principal minors of -Q")
lam = sp.symbols("l1:5")
RX = (sp.diag(*lam[:2]) - Q4.extract(X, X)).inv()
RY = (sp.diag(*lam[2:]) - Q4.extract(Y, Y)).inv()
o2 = sp.ones(2, 1)
p1, p2, al = (piX.T * RX * a)[0], (u.T * RX * o2)[0], (u.T * RX * a)[0]
q1, q2, be = (b.T * RY * o2)[0], (piY.T * RY * c)[0], (b.T * RY * c)[0]
EX, EY = (piX.T * RX * o2)[0], (piY.T * RY * o2)[0]
FQ, FQp = F(Q4, pi4, lam), F(Q4p, pi4, lam)
ok(sp.cancel(FQ - EX - EY - (p1 * q1 + p2 * q2 + al * q1 * q2 + be * p1 * p2) / (1 - al * be)) == 0,
   "gluing formula for F_Q")
ok(sp.cancel(FQ - FQp - (p1 - p2) * (q1 - q2) / (1 - al * be)) == 0,
   "F_Q - F_Q' = (p1 - p2)(q1 - q2)/(1 - alpha beta)")
ok(sp.cancel(p1 - p2) != 0 and sp.cancel(q1 - q2) != 0, "neither side of the cut is balanced")
ok(sp.cancel(FQ - F(reversal(Q4, pi4), pi4, lam)) == 0, "F_Q = F_{Q*}")
w = sp.symbols("w1:5")
W = sp.diag(*w)
M1, M2 = sp.eye(4), sp.eye(4)
diffs = []
for n in range(1, 4):
    M1, M2 = M1 * (Q4 - W), M2 * (Q4p - W)
    diffs.append(sp.expand((pi4 * M1 * sp.ones(4, 1))[0] - (pi4 * M2 * sp.ones(4, 1))[0]))
ok(diffs[0] == 0 and diffs[1] == 0, "pi (Q - W)^n 1 agrees for n = 1, 2")
ok(sp.expand(diffs[2] - R(29, 9673) * (w[0] - w[1]) * (w[2] - w[3])) == 0,
   "at n = 3 the difference is 29 (w1 - w2)(w3 - w4)/9673")
dS1 = sigma(Q4, pi4, 1) - sigma(Q4p, pi4, 1)
ok(sp.expand((sp.Matrix([w]) * dS1 * sp.Matrix(w))[0] / 2 - diffs[2]) == 0,
   "and it is (1/2) w^T (Sigma_1 - Sigma'_1) w")

# ------------------------------------------------------------------------------------------- (3)
print("(3) pi, Sigma_1 and Sigma_2 give Q up to time reversal for d <= 4")


def antisym_solutions(Q):
    d = Q.shape[0]
    pi = stationary(Q)
    D = sp.diag(*pi)
    A = D * Q
    K = (A - A.T) / 2
    xs = sp.symbols(f"x0:{d * (d - 1) // 2}")
    Kp = sp.zeros(d, d)
    it = iter(xs)
    for i in range(d):
        for j in range(i + 1, d):
            v = next(it)
            Kp[i, j], Kp[j, i] = v, -v
    eqs = list(Kp * sp.ones(d, 1)) + list(Kp * D.inv() * Kp - K * D.inv() * K)
    sols = sp.solve([e for e in eqs if e != 0], xs, dict=True)
    mats = [Kp.subs(sol) for sol in sols]
    return K, mats


def check_second_moments(Q, label):
    pi = stationary(Q)
    K, mats = antisym_solutions(Q)
    ok(all(M.free_symbols == set() for M in mats) and len(mats) == (1 if K == sp.zeros(*K.shape) else 2)
       and all(M == K or M == -K for M in mats),
       f"{label}: the only solutions are K' = K and K' = -K")
    # and then D Q' = (Sigma_1)/2 + K' gives Q' = Q or Q*
    for M in mats:
        Qp = sp.diag(*pi).inv() * (sigma(Q, pi, 1) / 2 + M)
        ok(Qp == Q or Qp == reversal(Q, pi), f"{label}: Q' = D^(-1)(Sigma_1/2 + K') is Q or Q*")
        ok(sigma(Qp, pi, 2) == sigma(Q, pi, 2), f"{label}: and it has the Sigma_2 of Q")


check_second_moments(Q4, "the four-state cut example")
check_second_moments(generator([[0, 3, 1, 0], [0, 0, 2, 1], [1, 0, 0, 5], [2, 1, 0, 0]]),
                     "a sparse four-state chain")
check_second_moments(generator([[0, R(1, 2), 2, 1], [3, 0, 1, R(1, 3)], [1, 1, 0, 4], [R(5, 2), 1, 1, 0]]),
                     "a four-state chain with all rates positive")
check_second_moments(generator([[0, 2, 1], [1, 0, 3], [4, 1, 0]]), "a three-state chain")
check_second_moments(generator([[0, 1, 1, 0], [1, 0, 1, 1], [1, 1, 0, 1], [0, 1, 1, 0]]),
                     "a reversible four-state chain")

# ------------------------------------------------------------------------------------------- (4)
print("(4) discrete second moments and one fixed N")
hh = sp.symbols("h", positive=True)
Q3 = generator([[0, 2, 1], [1, 0, 3], [4, 1, 0]])
pi3 = stationary(Q3)
P3 = sp.eye(3) + hh * Q3
D3 = sp.diag(*pi3)
for N in (2, 3, 4):
    E = sp.zeros(3, 3)
    for path in itertools.product(range(3), repeat=N):
        p = pi3[path[0]]
        for t_ in range(N - 1):
            p = p * P3[path[t_], path[t_ + 1]]
        n = [path.count(i) for i in range(3)]
        for i in range(3):
            for j in range(3):
                E[i, j] += p * n[i] * n[j]
    rhs = N ** 2 * D3 + sum((hh ** k * sp.binomial(N + 1, k + 2) * sigma(Q3, pi3, k) for k in range(1, N)),
                            sp.zeros(3, 3))
    ok((E - rhs).applyfunc(sp.expand) == sp.zeros(3, 3),
       f"E_pi[n n^T] = N^2 D + sum_k h^k C(N+1, k+2) Sigma_k at N = {N}")
k = sp.symbols("k")
S0 = sp.Matrix([[-3, 1, 2], [1, -3, 2], [2, 2, -4]]) / 1
Circ = sp.Matrix([[0, 1, -1], [-1, 0, 1], [1, -1, 0]])
Qk = S0 + k * Circ                            # uniform stationary law for every k
ok(sp.ones(1, 3) * Qk == sp.zeros(1, 3) and Qk * sp.ones(3, 1) == sp.zeros(3, 1),
   "Q_k = S + k C has the uniform stationary law for every k")
z3 = sp.symbols("z1:4")
laws = count_laws(sp.eye(3) + hh * Qk, sp.Matrix([[R(1, 3)] * 3]), z3, 3)
ok(sp.diff(laws[1], k) == 0, "the law of the counts at N = 2 does not depend on k, for every h")
ok(sp.expand(sp.diff(laws[2], k)) != 0, "the law of the counts at N = 3 depends on k")

print(f"\nall {CHECKS} checks passed")
