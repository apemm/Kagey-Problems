# Prop 3: Legendre identity, j2 and gamma, for the non-reversible cycle and a 4-state chain (g=3)
import numpy as np, mpmath as mp
from scipy.optimize import minimize, minimize_scalar
mp.mp.dps = 40

def rate(Qm, alpha):
    # I(alpha) = sup_u sum alpha_a (q_a - sum_{b!=a} q_ab u_b/u_a); occupation-homogeneous
    n = len(alpha)
    def neg(psi):
        psi = np.concatenate([[0.0], psi])
        val = 0.0
        for a in range(n):
            val += alpha[a]*(-Qm[a,a]) - alpha[a]*sum(Qm[a,b]*np.exp(psi[b]-psi[a]) for b in range(n) if b!=a)
        return -val
    res = minimize(neg, np.zeros(n-1), method="BFGS", options=dict(gtol=1e-13))
    return -res.fun

def J(Qm, G, i, beta, z):
    c = Qm[G, i]; rv = Qm[i, G]
    M = Qm[np.ix_(G,G)] + z*np.outer(c, rv)
    return rate(M, beta)

chains = {
 "cycle": np.array([[-3,2,1],[1,-3,2],[2,1,-3.]]),
 "4-state nonrev": np.array([[-4,1,2,1],[0.5,-2,1,0.5],[1,2,-4.5,1.5],[2,0.3,1,-3.3]]),
}
for name, Qm in chains.items():
    d = len(Qm); i = d-1; G = list(range(d-1))
    beta = np.ones(d-1)/(d-1)
    for S, x in [(10.0, 0.5), (20.0, 3.0)]:
        lhs = rate(Qm, np.concatenate([S*beta, [x]]))
        f = lambda lz: -(S*J(Qm, G, i, beta, np.exp(lz)) - x/np.exp(lz))
        r = minimize_scalar(f, bounds=(-12, 4), method="bounded", options=dict(xatol=1e-10))
        rhs = -Qm[i,i]*x - r.fun
        print(f"{name}: S={S}, x={x}: I_F(s,x) = {lhs:.10f}, q_i x + sup_z[S J - x/z] = {rhs:.10f}")
    # j2 by Richardson finite differences of J at z=0 vs formula
    import importlib.util, sys
    def Jz(z): return J(Qm, G, i, beta, z)
    hs = [0.02, 0.01, 0.005]
    d2 = [(Jz(2*hh) - 2*Jz(hh) + Jz(0))/hh**2 for hh in hs]   # forward second difference ~ J''(0) + h J'''(0) ...
    rich = [2*d2[k+1]-d2[k] for k in range(2)]
    # formula
    c = Qm[G, i]; rv = Qm[i, G]
    # tilt on G
    def tilt(beta):
        g = len(G); A = Qm[np.ix_(G,G)].copy(); np.fill_diagonal(A, 0)
        def neg(psi):
            psi = np.concatenate([[0.0], psi]); return sum(beta[a]*A[a,b]*np.exp(psi[b]-psi[a]) for a in range(g) for b in range(g))
        res = minimize(neg, np.zeros(g-1), method="BFGS", options=dict(gtol=1e-14))
        r = np.exp(np.concatenate([[0.0], res.x])); return r, beta/r, A
    r, l, A = tilt(beta)
    a = c@l; b = rv@r; ab = a*b
    gP = ab*(rv*r/b - c*l/a)
    K = l[:,None]*A*r[None,:]; K = K+K.T; L = np.diag(K.sum(1)) - K
    j2 = 0.5*gP@np.linalg.pinv(L)@gP
    print(f"{name}: ab = {ab:.6f}, -J'(0) FD = {-(Jz(1e-4)-Jz(-1e-4))/2e-4 if False else -(Jz(1e-4)-Jz(0))/1e-4:.6f}; "
          f"J''(0) formula 2 j2 = {2*j2:.6f}; FD second differences {['%.5f'%v for v in d2]}, Richardson {['%.5f'%v for v in rich]}; gamma - q_i = {j2/ab:.6f}")
