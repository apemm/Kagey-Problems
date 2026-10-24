import numpy as np, mpmath as mp
mp.mp.dps=30
def zeta_law(alpha, nmax):
    z=mp.zeta(alpha+1)
    f=np.zeros(nmax+2); T=np.zeros(nmax+2)
    for n in range(1,nmax+2):
        f[n]=float(mp.mpf(n)**(-(alpha+1))/z)
        T[n]=float(mp.zeta(alpha+1,n)/z)
    T[0]=1.0
    mu=float(mp.zeta(alpha)/z)
    return f,T,mu
def boundary(N,J,fp,Tp,fm,Tm,start):
    """F^{start}_n(n-m) for 1<=n<=N, 0<=m<=J; returns array E[m][n]."""
    A=[np.zeros(N+1) for _ in range(J+1)]; B=[np.zeros(N+1) for _ in range(J+1)]
    Tpz=Tp[:N+1].copy(); Tpz[0]=0.0
    fpz=fp[:N+1].copy(); fpz[0]=0.0
    E=np.zeros((J+1,N+1))
    for m in range(J+1):
        if start=='+':
            if m==0: A[0][0]=1.0
        for l in range(1,m+1):
            A[m]+=fm[l]*B[m-l]
        if start=='-' and m==0:
            B[0][0]=1.0
        else:
            B[m]=np.convolve(A[m],fpz)[:N+1]
        c=np.convolve(A[m],Tpz)[:N+1]   # c[x]=sum_k A[m][k] T_+(x-k)
        for n in range(max(m,1),N+1):
            v=c[n-m]
            for mm in range(m):
                v+=B[mm][n-m]*Tm[m-mm]
            E[m][n]=v
    return E
