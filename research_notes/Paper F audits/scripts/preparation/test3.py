import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from bl import *
# asymmetric laws to avoid accidental symmetry: plus zeta 1.5, minus zeta 1.3 shifted mixture
N=50; J=3
fp,Tp,mup=zeta_law(1.5,N+5); fm,Tm,mum=zeta_law(1.3,N+5)
s=mup+mum
Ep=boundary(N,J,fp,Tp,fm,Tm,'+'); Em=boundary(N,J,fp,Tp,fm,Tm,'-')
nup=Tp/s; num=Tm/s; nup[0]=num[0]=0
def P(j):
    v=0.0
    for d in range(1,j+1): v+=num[d]*Ep[j-d][N-d]
    for d in range(1,N):
        if j<=N-d: v+=nup[d]*Em[j][N-d]
    return v
fT=lambda n: sum(fp[a]*Tp[n-a] for a in range(1,n))
cf1=(Tm[1]/s)*Tp[N-1]+nup[N-1]+fm[1]*sum(nup[d]*Tp[N-1-d] for d in range(1,N-1))
cf2=(1/s)*(fm[1]*fT(N-2)+fp[N-2])+(Tm[2]/s)*Tp[N-2]+(Tp[N-2]/s)*Tm[2]+sum(nup[d]*(fm[2]*Tp[N-d-2]+fm[1]**2*fT(N-d-2)+fm[1]*fp[N-d-2]) for d in range(1,N-2))
print(cf1,P(1)); print(cf2,P(2))
