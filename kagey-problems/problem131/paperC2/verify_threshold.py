"""The least admissible horizon of the reversible design (the sentence after Theorem `thm:finite-horizon`).

The design of Section `sec:reversible-reconstruction` runs over 1/(4R) <= tau <= U = 8R/b^2, with
T = tau log N, and the chain has transition matrix I + (T/N) Q. Call N admissible if this matrix
is stochastic at every tau of the range. Its off-diagonal entries are nonnegative and its rows sum
to 1, so N is admissible exactly when 1 - T q_i/N >= 0 for every i at tau = U, that is when
N >= c log N with c = U q_max. For c > e the least admissible N >= 2 is the larger root N* of
N = c log N, so N* b^2 / log N* = 8 R q_max up to the rounding of N* to an integer.

We compute N* for two families of reversible generators with b decreasing and R fixed:

  * path:     3 states on a path, q_12 = q_21 = 1, q_23 = q_32 = b, R = 3;
  * triangle: 3 states, q_12 = q_21 = q_13 = q_31 = 1, q_23 = q_32 = b, R = 4;

with b = 2^-1, ..., 2^-8. Both are symmetric, so pi is uniform, S = -Q and sqrt(w_ij) = q_ij. For
each b we check that ||S||_2 <= R and min sqrt(w_ij) = b, so (R, b) are admissible design
constants, that I + (T/N*) Q is stochastic on a grid of the whole tau range and that
I + (T/(N*-1)) Q is not stochastic at tau = U, and that no N in [2, N*-1] is admissible. We print
N*, the ratio N* b^2 of N* against b^-2, and N* b^2 / (8 R q_max log N*), which lies in
[1, 1 + 1/(c log N*)]. The ratio N* b^2 is not constant. It grows like log(1/b), since
N* = c log N* with c of order b^-2, and the ratio of N* at b/2 and at b lies between 4 and 5.

Standard library only. Run:  py -I verify_threshold.py   (under a second)
"""

import math

CHECKS = 0


def ok(cond, what):
    global CHECKS
    if not cond:
        raise AssertionError(what)
    CHECKS += 1
    print("  ok   ", what)


def generator(rates, d):
    """Generator with q_ij = q_ji = rates[(i, j)] on the listed edges."""
    Q = [[0.0] * d for _ in range(d)]
    for (i, j), r in rates.items():
        Q[i][j] = Q[j][i] = r
    for i in range(d):
        Q[i][i] = -sum(Q[i][j] for j in range(d) if j != i)
    return Q


def sym_norm(S):
    """Spectral norm of a symmetric 3 x 3 matrix, by Jacobi rotations."""
    A = [row[:] for row in S]
    n = len(A)
    for _ in range(100):
        off = max(abs(A[p][q]) for p in range(n) for q in range(n) if p != q)
        if off < 1e-15:
            break
        for p in range(n):
            for q in range(p + 1, n):
                if abs(A[p][q]) < 1e-300:
                    continue
                theta = (A[q][q] - A[p][p]) / (2 * A[p][q])
                t = math.copysign(1.0, theta) / (abs(theta) + math.sqrt(theta * theta + 1))
                c = 1 / math.sqrt(t * t + 1)
                s = t * c
                for k in range(n):
                    akp, akq = A[k][p], A[k][q]
                    A[k][p], A[k][q] = c * akp - s * akq, s * akp + c * akq
                for k in range(n):
                    apk, aqk = A[p][k], A[q][k]
                    A[p][k], A[q][k] = c * apk - s * aqk, s * apk + c * aqk
    return max(abs(A[i][i]) for i in range(n))


def stochastic(Q, T, N):
    d = len(Q)
    P = [[(1.0 if i == j else 0.0) + T / N * Q[i][j] for j in range(d)] for i in range(d)]
    return all(x >= 0 for row in P for x in row) and all(abs(sum(row) - 1) < 1e-12 for row in P)


def least_admissible(c):
    """Least integer N >= 2 with N >= c log N, for c > e."""
    f = lambda n: n - c * math.log(n)
    lo, hi = math.ceil(c), math.ceil(c)
    while f(hi) < 0:
        hi *= 2
    while hi - lo > 1:          # f(lo) < 0 <= f(hi), and f increases on [c, oo)
        mid = (lo + hi) // 2
        if f(mid) < 0:
            lo = mid
        else:
            hi = mid
    return hi, f


def family(name, d, rates_of_b, R):
    print(f"Family {name}, R = {R}")
    print(f"  {'b':>10s} {'U':>12s} {'q_max':>8s} {'N*':>12s} {'N* b^2':>10s} "
          f"{'N* b^2/log N*':>14s} {'8 R q_max':>10s} {'N*/(c log N*)':>14s}")
    rows = []
    for e in range(1, 9):
        b = 2.0 ** -e
        Q = generator(rates_of_b(b), d)
        S = [[-x for x in row] for row in Q]
        qmax = max(-Q[i][i] for i in range(d))
        U = 8 * R / b ** 2
        c = U * qmax
        assert sym_norm(S) <= R and min(r for r in rates_of_b(b).values()) == b
        assert c > math.e
        N, f = least_admissible(c)
        L = math.log(N)
        assert f(2) < 0 and f(N - 1) < 0 and f(N) >= 0
        grid = [1 / (4 * R) + k * (U - 1 / (4 * R)) / 200 for k in range(201)]
        assert all(stochastic(Q, tau * L, N) for tau in grid)
        assert not stochastic(Q, U * math.log(N - 1), N - 1)
        ratio = N / (c * L)
        assert 1 <= ratio <= 1 + 1 / (c * L)
        rows.append((b, N))
        print(f"  {b:10.6f} {U:12.1f} {qmax:8.5f} {N:12d} {N * b * b:10.3f} "
              f"{N * b * b / L:14.6f} {8 * R * qmax:10.6f} {ratio:14.10f}")
    ok(True, f"{name}: ||S||_2 <= R and min sqrt(w_ij) = b for all 8 values of b")
    ok(True, f"{name}: I + (T/N*)Q is stochastic on a 201-point grid of [1/(4R), U], "
             "I + (T/(N*-1))Q is not at tau = U, and no N in [2, N*-1] is admissible")
    ok(True, f"{name}: N* b^2 / (8 R q_max log N*) lies in [1, 1 + 1/(c log N*)] for all 8 values")
    growth = [rows[k + 1][1] / rows[k][1] for k in range(len(rows) - 1)]
    print("  N*(b/2)/N*(b) =", ", ".join(f"{g:.3f}" for g in growth))
    ok(all(4 < g < 5 for g in growth), f"{name}: N* grows by a factor between 4 and 5 when b is halved")
    nb2 = [N * b * b for b, N in rows]
    ok(all(nb2[k + 1] > nb2[k] for k in range(len(nb2) - 1)),
       f"{name}: N* b^2 increases as b decreases (the factor log N*)")
    print()


def main():
    family("path", 3, lambda b: {(0, 1): 1.0, (1, 2): b}, 3)
    family("triangle", 3, lambda b: {(0, 1): 1.0, (0, 2): 1.0, (1, 2): b}, 4)
    print(f"All {CHECKS} checks passed.")


if __name__ == "__main__":
    main()
