import sys, itertools
from math import comb, gcd
from collections import defaultdict

def run(n, T):
    T = sorted(T); m = len(T); Ts = set(T)
    # Sidon check
    diffs = [a-b for a in T for b in T if a > b]
    assert len(diffs) == len(set(diffs)), "not Sidon"
    G = [(x, y) for x in range(1, n+1) for y in T]
    Gs = set(G)
    ing = lambda P: 1 <= P[0] <= n and 1 <= P[1] <= n
    dmax = max(sum(1 for d in range(1, k+1) if k % d == 0) for k in range(1, n*n+1)) if n <= 40 else None
    print(f"n={n} T={T} m={m} |G|={len(G)} dmax={dmax}")

    # right angles
    byP = defaultdict(list)
    rect_ord = 0; tilted_rect = 0
    n_ax = n_tl = 0
    for V in G:
        others = [U for U in G if U != V]
        for i in range(len(others)):
            U = others[i]; ux, uy = U[0]-V[0], U[1]-V[1]
            for j in range(i+1, len(others)):
                W = others[j]; wx, wy = W[0]-V[0], W[1]-V[1]
                if ux*wx + uy*wy: continue
                P = (U[0]+W[0]-V[0], U[1]+W[1]-V[1])
                axis = (ux == 0 or uy == 0)
                if P in Gs:
                    rect_ord += 1
                    if not axis: tilted_rect += 1
                if not ing(P): continue
                if axis: n_ax += 1
                else:
                    n_tl += 1
                    assert P[1] not in Ts, "tilted completion row in T"
                    assert ux and uy and wx and wy
                byP[P].append((axis, frozenset((V, U, W))))
    NH = rect_ord // 4
    print(" rectangles in G:", NH, "formula", comb(n, 2)*comb(m, 2), "tilted:", tilted_rect)
    print(" axis right angles (completion in grid):", n_ax, "formula", n*m*(n-1)*(m-1))
    print(" tilted right angles (completion in grid):", n_tl, "bound m^3 n dmax =", m**3*n*dmax)
    aa = at = tt = 0
    six_aa = set(); six_tt = set(); tt_share2 = 0
    for P, L in byP.items():
        for i in range(len(L)):
            for j in range(i+1, len(L)):
                a1, s1 = L[i]; a2, s2 = L[j]
                u = s1 | s2
                if a1 and a2:
                    aa += 1
                    if len(u) == 6: six_aa.add(u)
                elif a1 or a2:
                    at += 1
                else:
                    tt += 1
                    if len(u) == 6: six_tt.add(u)
                    else: tt_share2 += 1
    print(" axis-axis pairs:", aa, "formula", n*m*comb((n-1)*(m-1), 2))
    print(" distinct axis 6-sets:", len(six_aa), "formula 6C(n,3)C(m,3) =", 6*comb(n, 3)*comb(m, 3))
    print(" axis-tilted pairs:", at)
    print(" tilted-tilted pairs:", tt, "distinct 6-sets:", len(six_tt), "non-6-point:", tt_share2,
          "bound 2 dmax^2 n m^4 =", 2*dmax**2*n*m**4, " n*m^4 =", n*m**4)

    # F configurations
    NF = 0; Fsets = set()
    for i in range(len(G)):
        A = G[i]
        for j in range(i+1, len(G)):
            B = G[j]
            vx, vy = B[0]-A[0], B[1]-A[1]
            g = gcd(abs(vx), abs(vy)); px, py = -vy//g, vx//g
            L2 = vx*vx + vy*vy
            for k in itertools.chain(range(-n, 0), range(1, n+1)):
                P = (A[0]+k*px, A[1]+k*py); Q = (B[0]+k*px, B[1]+k*py)
                if not (ing(P) and ing(Q)): continue
                for C in G:
                    D = (P[0]+Q[0]-C[0], P[1]+Q[1]-C[1])
                    if D not in Gs or not (C < D): continue
                    if (C[0]-D[0])**2 + (C[1]-D[1])**2 != L2: continue
                    if C == P or C == Q: continue
                    assert len({A, B, C, D}) == 4
                    assert abs(D[1]-C[1]) != abs(B[1]-A[1]), "K=0 case occurred"
                    NF += 1; Fsets.add(frozenset((A, B, C, D)))
    print(" F configurations:", NF, "distinct 4-sets:", len(Fsets), "bound n m^4 dmax/2 =", n*m**4*dmax/2, " n*m^4 =", n*m**4)

run(12, [1, 2, 5, 11])
run(24, [1, 2, 5, 10, 16, 23])
if len(sys.argv) > 1:
    run(34, [1, 2, 5, 10, 16, 23, 33])
