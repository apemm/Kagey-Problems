import numpy as np, mpmath as mp, sys
a=2.5; z=float(mp.zeta(a))
NMAX=int(sys.argv[1]); R=int(sys.argv[2])
n=np.arange(NMAX+2,dtype=float)
f=np.zeros(NMAX+2); f[1:]=n[1:]**(-a)/z
T=np.zeros(NMAX+2); T[1:]=[float(mp.zeta(a,k))/z for k in range(1,NMAX+2)]
mu=float(mp.zeta(a-1))/z; s=2*mu; alpha=1.5
# minus kernels up to R
L=NMAX+1
U=[np.zeros(L) for _ in range(R+2)]; U[0][0]=1.0
for r in range(1,R+2): U[r]=np.convolve(U[r-1],f[:L])[:L]
u=sum(U[r] for r in range(1,R+2)); u[0]=1.0   # valid for index<=R+1
v=sum(r*U[r] for r in range(1,R+2))
Tc=T[:L]
CT=[np.convolve(U[r],Tc)[:L] for r in range(R+1)]  # CT[r][m]=sum_k U_r(k) T(m-k)
def P(N,j):
    tot=0.0
    for r in range(0,j+1): tot+=U[r][j]*CT[r][N-j]
    for m in range(1,j+1):
        for r in range(0,j-m+1): tot+=T[m]*U[r][j-m]*U[r+1][N-j]
    return tot
def C(j): return alpha*(j*u[j]+2*mu*v[j]+u[:j].sum())
if __name__=='__main__':
    mode=sys.argv[3]
    if mode=='cj':
        print('limit',2*alpha*s/mu**2)
        for j in [5,10,20,40,80,160,320]:
            if j<=R: print(j, C(j)/j)
        for j in [40,160,640]:
            if j<=R: print('ren',j,(u[j]-1/mu)/(j*T[j]/(mu**2*(alpha-1))))
    if mode=='exp':
        for N in [1000,2000,4000,8000]:
            if N>NMAX: continue
            for j in [1,2,3,5]:
                e=(P(N,j)/T[N]-u[j])*N
                print(N,j,'N(P/T-u)=',round(e,4),'C(j)=',round(C(j),4))
    if mode=='table':
        for N in [600,1200,2400,4000,8000]:
            if N>NMAX: continue
            Jm=min(R, int(N/2))
            vals=[P(N,j)/T[N] for j in range(0,Jm+1)]
            js=int(np.argmin(vals))
            ref=[u[j]+C(j)/N for j in range(0,Jm+1)]; iN=int(np.argmin(ref))
            lN=next(j for j in range(1,NMAX) if T[j]<2*alpha*s/N)
            print(N,'j*',js,'i_N',iN,'l_N',lN,'ratio',round(N*T[js]/(2*alpha*s),3),'Jm',Jm)
    if mode=='unif':
        N=int(sys.argv[4])
        for j in [1,5,10,20,40,80,R]:
            if j<=R: print(N,j,'(N/j)*err=',(N/j)*(P(N,j)/T[N]-u[j]-C(j)/N))
