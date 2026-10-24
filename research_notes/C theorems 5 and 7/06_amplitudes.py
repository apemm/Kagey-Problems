"""Second-order amplitudes on the principal-minor fiber (route T4, items 4b and 4d).

K_F(v) = (mu_F . r)(l . 1) * G_F(v), with l.r = 1, r and l the Perron vectors of A_F - diag v,
A = -Q, and the Gaussian factor G_F(v) = (2 pi)^{-(k-1)/2} / sqrt(det Sigma) computed two ways:
from Definition 4.1 (the matrix Z of the tilted generator) and from Proposition 4.9(b)
(prod(rho - lambda)/sqrt(tree(f + f^T))).
States are 0-indexed here and 1-indexed in the note: X = {0,1} here is X = {1,2} there.
"""
import itertools
import numpy as np
from scipy.optimize import minimize

np.set_printoptions(precision=6, suppress=True)


def perron(B):
    """Smallest real eigenvalue of an irreducible Z-matrix B, positive right/left vectors, l.r = 1."""
    w, V = np.linalg.eig(B)
    j = np.argmin(np.real(w))
    lam = np.real(w[j])
    r = np.real(V[:, j]); r = r / r.sum()
    w2, U = np.linalg.eig(B.T)
    j2 = np.argmin(np.real(w2))
    l = np.real(U[:, j2]); l = l / (l @ r)
    assert (r > 0).all() and (l > 0).all()
    return lam, r, l


def tree_count(C):
    L = np.diag(C.sum(1)) - C
    return np.linalg.det(L[1:, 1:]) if C.shape[0] > 1 else 1.0


def face_data(Q, F, v, mu):
    F = list(F); k = len(F)
    A = -Q
    B = A[np.ix_(F, F)] - np.diag(v[F])
    lam, r, l = perron(B)
    alpha = l * r
    amp = (mu[F] @ r) * l.sum()
    if k == 1:
        return dict(lam=lam, alpha=alpha, amp=amp, gauss=1.0, gauss2=1.0, K=amp, r=r, l=l)
    off = Q[np.ix_(F, F)].copy(); np.fill_diagonal(off, 0)
    theta = (off @ r) / r
    Qhat = np.diag(1 / r) @ (off - np.diag(theta)) @ np.diag(r)
    one = np.ones(k)
    Z = np.linalg.inv(np.outer(one, alpha) - Qhat) - np.outer(one, alpha)
    D = np.diag(alpha)
    Gam = D @ Z + Z.T @ D
    Sig = Gam[1:, 1:]
    gauss = (2 * np.pi) ** (-(k - 1) / 2) / np.sqrt(np.linalg.det(Sig))
    ev = sorted(np.linalg.eigvals(B), key=lambda z: abs(z - lam))[1:]
    prod = np.real(np.prod([z - lam for z in ev]))
    f = np.outer(l, r) * off
    gauss2 = (2 * np.pi) ** (-(k - 1) / 2) * prod / np.sqrt(tree_count(f + f.T))
    return dict(lam=lam, alpha=alpha, amp=amp, gauss=gauss, gauss2=gauss2, K=amp * gauss, r=r, l=l)


def stationary(Q):
    w, V = np.linalg.eig(Q.T)
    j = np.argmin(abs(w)); pi = np.real(V[:, j]); return pi / pi.sum()


def reversal(Q):
    pi = stationary(Q)
    return np.diag(1 / pi) @ Q.T @ np.diag(pi)


def minors(A):
    d = A.shape[0]
    return {S: np.linalg.det(A[np.ix_(S, S)]) for r in range(1, d + 1)
            for S in itertools.combinations(range(d), r)}


def irreducible(Q, H):
    H = list(H); k = len(H)
    R = (Q[np.ix_(H, H)] > 1e-12) | np.eye(k, dtype=bool)
    for _ in range(k):
        R = R | ((R.astype(int) @ R.astype(int)) > 0)
    return R.all()


# ------------------------------------------------------------ the four-state example
p = np.array([1., 2.]); q = np.array([1., 3.]); u = np.array([2., 1.]); vv = np.array([1., 1.])
Q = np.zeros((4, 4))
Q[0, 1] = 0.7; Q[1, 0] = 1.3; Q[2, 3] = 0.4; Q[3, 2] = 2.0
Q[np.ix_([0, 1], [2, 3])] = np.outer(p, q); Q[np.ix_([2, 3], [0, 1])] = np.outer(u, vv)
np.fill_diagonal(Q, 0); np.fill_diagonal(Q, -Q.sum(1))
A = -Q
X, Y = [0, 1], [2, 3]
Ap = np.zeros((4, 4))
Ap[np.ix_(X, X)] = A[np.ix_(X, X)]; Ap[np.ix_(Y, Y)] = A[np.ix_(Y, Y)].T
Ap[np.ix_(X, Y)] = -np.outer(p, u); Ap[np.ix_(Y, X)] = -np.outer(q, vv)
lam0, h, _ = perron(Ap)
Qp = -(np.diag(1 / h) @ Ap @ np.diag(h))
Qs = reversal(Q)
pi = stationary(Q)
GENS = {"Q": Q, "Q*": Qs, "Qc": Qp}   # Qc is the normalized cut-transpose Q'


def amps(F, v, mu):
    return {g: face_data(GENS[g], F, v, mu) for g in GENS}


def main():
    print("pi =", pi)
    s0 = q.sum() / (u @ pi[Y])
    print("h/h_0 =", h / h[0], "  predicted (1, 1, s0 pi_Y) =", np.r_[1, 1, s0 * pi[Y]])
    for a, b in [("Q", "Q*"), ("Q", "Qc"), ("Q*", "Qc")]:
        mA, mB = minors(-GENS[a]), minors(-GENS[b])
        print(f"max |principal minor difference| {a} vs {b}: {max(abs(mA[S]-mB[S]) for S in mA):.2e}")
    print("Q' =\n", Qp)
    print("Q* =\n", Qs)
    print("max|Q'_YY - Q*_YY| =", np.abs(Qp[np.ix_(Y, Y)] - Qs[np.ix_(Y, Y)]).max(),
          "  max|Q'_XX - Q_XX| =", np.abs(Qp[np.ix_(X, X)] - Q[np.ix_(X, X)]).max())

    mu = np.array([0.4, 0.3, 0.2, 0.1])
    faces = [(0, 1, 2), (0, 1, 3), (1, 2, 3), (0, 2, 3), (0, 1, 2, 3), (0, 1), (2, 3), (0, 2), (1, 3)]
    fields = {"v=0": np.zeros(4), "v=(1,0,0,0)": np.array([1., 0, 0, 0]),
              "v=(0,0,1,-1)": np.array([0, 0, 1., -1.]),
              "v=(0.5,-1,0.3,0.8)": np.array([0.5, -1, 0.3, 0.8])}
    print("\nAmplitudes (mu.r)(l.1), mu =", mu, "; faces 1-indexed; Qc = Q'")
    md_def = 0; md_fib = 0
    for F in faces:
        if not irreducible(Q, F):
            print("  face", [i + 1 for i in F], "reducible, skipped")
            continue
        name = "{" + ",".join(str(i + 1) for i in F) + "}"
        for fn, v in fields.items():
            d = amps(F, v, mu)
            for g in GENS:
                md_def = max(md_def, abs(d[g]["gauss"] - d[g]["gauss2"]) / d[g]["gauss"])
                md_fib = max(md_fib, abs(d[g]["gauss"] - d["Q"]["gauss"]) / d["Q"]["gauss"],
                             abs(d[g]["lam"] - d["Q"]["lam"]),
                             np.abs(d[g]["alpha"] - d["Q"]["alpha"]).max())
            aQ, aS, aC = d["Q"]["amp"], d["Q*"]["amp"], d["Qc"]["amp"]
            print(f"  F={name:10s} {fn:20s} Q={aQ:.6f} Q*={aS:.6f} Q'={aC:.6f}"
                  f"  Q'-Q={aC-aQ:+.2e} Q'-Q*={aC-aS:+.2e}  K_F(Q)={d['Q']['K']:.6f}")
    print(f"max rel. difference of the Gaussian factor, Def 4.1 vs Prop 4.9(b): {md_def:.2e}")
    print(f"max difference across the fiber of lambda_F, alpha*_F, Gaussian factor: {md_fib:.2e}")

    print("\nStationary start mu = pi, face V")
    for fn, v in fields.items():
        d = amps((0, 1, 2, 3), v, pi)
        print(f"  {fn:20s} Q={d['Q']['amp']:.10f} Q*={d['Q*']['amp']:.10f} Q'={d['Qc']['amp']:.10f}")

    print("\nBlockwise formula on V: r' ~ H^{-1}(r_X, s l_Y), s = (b.r_Y)/(c.l_Y) = (d.r_X)/(a.l_X)")
    for fn, v in fields.items():
        _, r, l = perron(A - np.diag(v))
        s = (q @ r[Y]) / (u @ l[Y]); s2 = (vv @ r[X]) / (p @ l[X])
        rp_pred = np.r_[r[X], s * l[Y]] / h
        lp_pred = np.r_[l[X], r[Y] / s] * h
        _, rp, lp = perron(-Qp - np.diag(v))
        e1 = np.abs(rp / rp.sum() - rp_pred / rp_pred.sum()).max()
        e2 = np.abs(lp / lp.sum() - lp_pred / lp_pred.sum()).max()
        print(f"  {fn:20s} s - s' = {s-s2:.1e}; r' error {e1:.1e}; l' error {e2:.1e};"
              f" (r_pred.l_pred) - (r.l) = {rp_pred@lp_pred - r@l:.1e}")

    print("\nW = span{g_1(v) - g_2(v)}, g = r (l.1), 60 random fields, face V")
    rng = np.random.default_rng(1)
    vs = [rng.normal(size=4) for _ in range(60)]
    for a, b in [("Q", "Q*"), ("Q", "Qc"), ("Q*", "Qc")]:
        Wm = []
        for v in vs:
            _, r1, l1 = perron(-GENS[a] - np.diag(v)); _, r2, l2 = perron(-GENS[b] - np.diag(v))
            Wm.append(r1 * l1.sum() - r2 * l2.sum())
        Wm = np.array(Wm)
        _, sv, Vt = np.linalg.svd(Wm)
        perp = Vt[-1]
        print(f"  {a} vs {b}: singular values {sv}; W-perp (sum 1) = {perp/perp.sum()}")

    print("\nKilled blocks of Q' against Q and Q*")
    for F in [(0, 1), (2, 3), (0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]:
        F = list(F)
        print(f"  F={[i+1 for i in F]}: max|Q'_F - Q_F| = {np.abs(Qp[np.ix_(F,F)]-Q[np.ix_(F,F)]).max():.4f}, "
              f"max|Q'_F - Q*_F| = {np.abs(Qp[np.ix_(F,F)]-Qs[np.ix_(F,F)]).max():.4f}")

    print("\nPair faces: agreement test mu_i q'_ij = mu_j q_ji (Q vs Q*) on mu = pi and on mu above")
    for (i, j) in [(0, 1), (2, 3), (0, 2), (1, 3)]:
        for m, nm in [(pi, "pi"), (mu, "mu")]:
            dif = max(abs(face_data(Q, (i, j), v, m)["amp"] - face_data(Qs, (i, j), v, m)["amp"])
                      for v in fields.values())
            print(f"  pair {{{i+1},{j+1}}}, start {nm}: q*_ij - q_ij = {Qs[i,j]-Q[i,j]:+.4f},"
                  f" max amp difference over fields = {dif:.2e}")

    # ------------------------------------------------------------ three states (item 4d)
    print("\nStationary start, face V: Amp(Q') - Amp(Q) = (a - sig c)(b/sig - e),"
          " a = pi_X.r_X, c = l_X.1, b = pi_Y.r_Y, e = l_Y.1")
    s0 = q.sum() / (u @ pi[Y])
    for v in [np.array([1., 0, 0, 0]), np.array([1., -1, 0, 0]), np.array([0, 0, 1., -1]),
              np.array([0, 0, 2., 0]), np.array([0.5, -1, 0.3, 0.8]), np.array([1., 0, 1, 0])]:
        _, r, l = perron(A - np.diag(v)); sig = ((q @ r[Y]) / (u @ l[Y])) / s0
        a_, c_, b_, e_ = pi[X] @ r[X], l[X].sum(), pi[Y] @ r[Y], l[Y].sum()
        direct = face_data(Qp, (0, 1, 2, 3), v, pi)["amp"] - face_data(Q, (0, 1, 2, 3), v, pi)["amp"]
        print(f"  v={v}: a - sig c = {a_-sig*c_:+.3e}, b/sig - e = {b_/sig-e_:+.3e},"
              f" product = {(a_-sig*c_)*(b_/sig-e_):+.3e}, direct = {direct:+.3e}")

    print("\nThree states. Uniform 3-cycle (Kim and Landim, Example 5.4)")
    C = np.zeros((3, 3)); C[0, 1] = C[1, 2] = C[2, 0] = 1.0; np.fill_diagonal(C, -C.sum(1))
    Cs = reversal(C)
    print("  reversal equals transpose:", np.allclose(Cs, C.T))
    mC, mCs = minors(-C), minors(-Cs)
    print("  max principal-minor difference:", max(abs(mC[S] - mCs[S]) for S in mC))
    d0 = face_data(C, (0, 1, 2), np.zeros(3), np.ones(3) / 3)
    print(f"  K_V(0), mu uniform: {d0['K']:.10f}; Prop 4.9(d) and 4.10 at b=1: 3 sqrt3/(2 pi) = {3*np.sqrt(3)/(2*np.pi):.10f}")
    for v in [np.array([0.3, -0.2, 0.5]), np.array([1.0, 0.0, -1.0])]:
        lamv = perron(-C - np.diag(v))[0]
        f = lambda x: (lambda m: 1 - 3 * np.prod(m) ** (1 / 3) - v @ m)(np.exp(x) / np.exp(x).sum())
        val = minimize(f, np.zeros(3), method="Nelder-Mead",
                       options={"xatol": 1e-12, "fatol": 1e-14, "maxiter": 20000}).fun
        print(f"  v={v}: lambda_V(v) = {lamv:.10f}; min_m [I_KL(m) - v.m] = {val:.10f}")
    for mu3 in [np.ones(3) / 3, np.array([0.5, 0.3, 0.2])]:
        print(f"  mu = {mu3}")
        for v in [np.zeros(3), np.array([1.0, 0, 0]), np.array([0.3, -0.2, 0.5]), np.array([0, 1.0, 0])]:
            a1 = face_data(C, (0, 1, 2), v, mu3)["amp"]; a2 = face_data(Cs, (0, 1, 2), v, mu3)["amp"]
            print(f"    v={v}: amp Q = {a1:.8f}, amp Q* = {a2:.8f}, diff = {a1-a2:+.2e}")

    print("\nThree states, non-reversible, all pair products positive")
    R = np.array([[0, 2.0, 0.5], [0.3, 0, 1.5], [1.2, 0.4, 0]]); np.fill_diagonal(R, -R.sum(1))
    Rs = reversal(R)
    qd = -np.diag(R)
    w = lambda i, j: R[i, j] * R[j, i]
    c, cp = R[0, 1] * R[1, 2] * R[2, 0], R[0, 2] * R[2, 1] * R[1, 0]
    ssum = qd[0] * qd[1] * qd[2] - qd[0] * w(1, 2) - qd[1] * w(0, 2) - qd[2] * w(0, 1)
    print(f"  c + c' = {c+cp:.10f}; q1q2q3 - q1w23 - q2w13 - q3w12 = {ssum:.10f}")
    print(f"  c c'   = {c*cp:.10f}; w12 w23 w13 = {w(0,1)*w(1,2)*w(0,2):.10f}")
    print(f"  Q* product along 1->2->3->1 = {Rs[0,1]*Rs[1,2]*Rs[2,0]:.10f}; c' = {cp:.10f}")
    mR, mRs = minors(-R), minors(-Rs)
    print("  max principal-minor difference Q vs Q*:", max(abs(mR[S] - mRs[S]) for S in mR))
    piR = stationary(R)
    for mu3 in [piR, np.array([0.5, 0.3, 0.2])]:
        print(f"  mu = {np.round(mu3, 6)}")
        for F in [(0, 1, 2), (0, 1), (1, 2), (0, 2)]:
            for v in [np.zeros(3), np.array([1.0, 0, -0.5])]:
                a1 = face_data(R, F, v, mu3)["amp"]; a2 = face_data(Rs, F, v, mu3)["amp"]
                print(f"    F={[i+1 for i in F]} v={v}: amp Q = {a1:.8f}, amp Q* = {a2:.8f}, diff = {a1-a2:+.2e}")


if __name__ == "__main__":
    main()
