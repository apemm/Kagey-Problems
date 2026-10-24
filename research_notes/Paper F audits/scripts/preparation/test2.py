import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from bl import *
J=5
def renewal(f,J):
    u=np.zeros(J+1); u[0]=1
    for j in range(1,J+1): u[j]=sum(f[i]*u[j-i] for i in range(1,j+1))
    return u
def prep_boundary(N,nup,num,Ep,Em,Qp):
    """P_N(N-j), j<=J, by the first-run decomposition."""
    out=[]
    for j in range(J+1):
        v=Qp if j==0 else 0.0
        for d in range(1,j+1): v+=num[d]*Ep[j-d][N-d]
        for d in range(1,N): 
            if j<=N-d: v+=nup[d]*Em[j][N-d]
        out.append(v)
    return out
for N in (60,1200,2400):
    f,T,mu=zeta_law(1.5,N+5); s=2*mu; u=renewal(f,J)
    Ep=boundary(N,J,f,T,f,T,'+'); Em=boundary(N,J,f,T,f,T,'-')
    nu=T/s; nu[0]=0
    Qp=(mu-sum(T[1:N]))/s
    P=prep_boundary(N,nu,nu,Ep,Em,Qp)
    kst=[(2/s)*(1+mu*u[j]) for j in range(J+1)]
    print('N',N,'stationary ratio P/(T kst):',[round(P[j]/(T[N]*kst[j]),5) for j in (1,2,5)])
    if N==60:
        cf=(2/s)*T[N-1]+(f[1]/s)*sum(T[d]*T[N-1-d] for d in range(1,N-1))
        print(' closed stationary P(N-1)',cf,P[1])
    # length-2 counterexample: pi_+=0.5 with nu_+=0.5 f, nu_-(2)=0.5
    nup=0.5*f.copy(); nup[0]=0; num=np.zeros(N+2); num[2]=0.5
    P2=prep_boundary(N,nup,num,Ep,Em,0.5*T[N])
    pred=[0.5*u[j]+0.5*(u[j-2] if j>=2 else 0) for j in range(J+1)]
    print(' len-2: P/T',[round(P2[j]/T[N],5) for j in range(1,J+1)],' pred',[round(x,5) for x in pred[1:]],' fresh u',[round(x,5) for x in u[1:]])
